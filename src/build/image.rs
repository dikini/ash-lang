//! Matching-compiler private Core construction records.
//!
//! This initial carrier deliberately refuses unsupported metadata. It contains
//! flat indices and bytes, never parser trees, recursive Type serialization or
//! validated capabilities. Restoration builds unchecked Core and invokes the
//! existing modular validator. These records are not a stable file format.

use std::{
    borrow::Borrow,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::{
    core::{
        CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind, NodeId, Primitive,
        PureComputation, PureExprKind, PureValue, ValidatedProgram,
    },
    integer::Integer,
    module::ModuleId,
    resolved::{
        BinderId, ResolvedConstructor, ResolvedEffectBuffer, ResolvedNominalDeclarationKind,
        ResolvedNominalType, ResolvedRegistry,
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
    EffectOperation,
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
                write!(
                    formatter,
                    "Private program image does not support {feature:?}"
                )
            }

            Self::Resource => formatter.write_str("Private program image exhausted resources"),
            Self::InvalidRecord => {
                formatter.write_str("Private program image record is inconsistent")
            }
            Self::UnsupportedFormat => {
                formatter.write_str("Private program image format does not match this compiler")
            }
            Self::InvalidEncoding => formatter
                .write_str("Private program image encoding is malformed or has trailing bytes"),
            Self::SourceAdmission => {
                formatter.write_str("Private program image source admission refused")
            }
            Self::RegistryAdmission => {
                formatter.write_str("Private program image registry admission refused")
            }
            Self::CoreAdmission(error) => {
                write!(formatter, "Pure image Core admission refused: {error}")
            }
            Self::Validation(error) => write!(formatter, "Pure image validation refused: {error}"),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
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
    role: ModuleRoleRecord,
    path: Slice,
    text: Slice,
}

/// One complete original arena and its occurrence root, separate from the
/// shared wire allocation. Every node and edge is retained, including nonroot
/// nodes; restoring a view never substitutes another annotation's arena.
#[derive(Clone, Copy, Debug)]
struct ProvenanceViewRecord {
    nodes: Slice,
    children: Slice,
    root: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct SpanRecord {
    source: u32,
    start: u32,
    end: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum OriginRecord {
    Source(SpanRecord),
    Generated { cause: u32, reason: GeneratedReason },
    Related { primary: u32, related: Slice },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct NominalId {
    module: u32,
    local: u32,
}

#[derive(Clone, Copy, Debug)]
struct ConstructorIdentity {
    owner: NominalId,
    local: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum BinderIdentity {
    Resolved { module: u32, local: u32 },
    Generated(u32),
}

#[derive(Clone, Copy, Debug)]
struct CellAcquisitionRecord {
    module: u32,
    identity: TypeVariableIdentity,
    handle: BinderIdentity,
    provider_module: u32,
    provider_local: u32,
    read: BinderIdentity,
    write: BinderIdentity,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum TypeTag {
    Variable(TypeVariableIdentity),
    Application,
    Forall {
        parameters: Slice,
    },
    EffectfulFunction,
    ArgumentType,
    ArgumentRow,
    Resource(ResourceIdentity),
    Instance(EffectIdentity),
    Row {
        known: u32,
        tail: Option<TypeVariableIdentity>,
    },

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

// The retained and borrowed keys use the same exact flat representation. A
// lookup never owns the scratch child slice, or compares semantic Type trees.
trait StructuralKeyView {
    fn parts(&self) -> (TypeTag, &[u32]);
}

struct StructuralKey(TypeTag, Box<[u32]>);
struct StructuralProbe<'a>(TypeTag, &'a [u32]);

impl StructuralKeyView for StructuralKey {
    fn parts(&self) -> (TypeTag, &[u32]) {
        (self.0, &self.1)
    }
}
impl StructuralKeyView for StructuralProbe<'_> {
    fn parts(&self) -> (TypeTag, &[u32]) {
        (self.0, self.1)
    }
}
impl<'a> Borrow<dyn StructuralKeyView + 'a> for StructuralKey {
    fn borrow(&self) -> &(dyn StructuralKeyView + 'a) {
        self
    }
}
fn hash_structural_key(key: &dyn StructuralKeyView, state: &mut impl Hasher) {
    let (tag, children) = key.parts();
    tag.hash(state);
    children.hash(state);
}
fn same_structural_key(left: &dyn StructuralKeyView, right: &dyn StructuralKeyView) -> bool {
    left.parts() == right.parts()
}
impl Hash for StructuralKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_structural_key(self, state);
    }
}
impl PartialEq for StructuralKey {
    fn eq(&self, other: &Self) -> bool {
        same_structural_key(self, other)
    }
}
impl Eq for StructuralKey {}
impl Hash for dyn StructuralKeyView + '_ {
    fn hash<H: Hasher>(&self, state: &mut H) {
        hash_structural_key(self, state);
    }
}
impl PartialEq for dyn StructuralKeyView + '_ {
    fn eq(&self, other: &Self) -> bool {
        same_structural_key(self, other)
    }
}
impl Eq for dyn StructuralKeyView + '_ {}

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
    IntegerMagnitude {
        negative: bool,
        bytes: Slice,
    },
    RegionBuffer {
        api: u32,
        context: u32,
        operand: Option<u32>,
        right: Option<u32>,
        source: u8,
        module: Option<u32>,
        operation: u8,
        bytes: Slice,
    },
    RegionValueRequest {
        api: u32,
        fields: u32,
    },
    RegionTuple {
        constructor: Option<ConstructorIdentity>,
        api: u32,
        context: u32,
        storage: u32,
        fields: Slice,
    },
    RegionBinding {
        module: u32,
        operation: u8,
        owner: Option<TypeVariableIdentity>,
        address_module: Option<u32>,
    },
    Region {
        entry: bool,
        api: u32,
        identity: TypeVariableIdentity,
        access: u32,
        preceding: u32,
        provider: u32,
        body: u32,
    },
    RegionAllocate {
        api: u32,
        context: u32,
        request: u32,
    },
    RegionHost {
        module: u32,
        owner: TypeVariableIdentity,
        release: bool,
    },
    CellScope {
        acquisition: CellAcquisitionRecord,
        handle: u32,
        initializer: u32,
        body: u32,
    },
    Cleanup {
        callback: BinderIdentity,
        body: u32,
        action: u32,
        span: SpanRecord,
        action_span: SpanRecord,
    },
    Registration {
        handler: u32,
        callback: BinderIdentity,
        body: u32,
        span: SpanRecord,
    },
    Handler(u32),
    Resume {
        handler: u32,
        owner: u32,
        available: bool,
        value: u32,
    },
    Discard {
        handler: u32,
        owner: u32,
        available: bool,
    },

    StringIntrinsic {
        module: u32,
        operation: u8,
    },
    AddressIntrinsic {
        module: u32,
        operation: u8,
    },
    BytesIntrinsic {
        module: u32,
        operation: u8,
    },
    Request {
        effect: u32,
        operation: OperationIdentity,
        operand: u32,
    },
    NativeInterpret {
        body: u32,
        interpretations: Slice,
    },
    TypeAbstraction {
        parameters: Slice,
        body: u32,
    },
    TypeApplication {
        function: u32,
        arguments: Slice,
        row_arguments: Slice,
    },
    Integer(i64),
    UnsignedInteger(u64),
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
    effects: Option<u32>,
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

/// Append-only shared-table extents sealed before executable graph encoding.
/// These copied counts select the original declaration facts for expectations;
/// they grant no registry or execution authority.
#[derive(Clone, Copy, Debug)]
struct NativeFactPrefixes {
    bytes: u32,
    spans: u32,
    origins: u32,
    types: u32,
    type_children: u32,
    kinds: u32,
    parameters: u32,
    quantifiers: u32,
    method_catalogs: u32,
    source_methods: u32,
    method_variables: u32,
    inherited_parameters: u32,
}

impl NativeFactPrefixes {
    fn seal(image: &PureImage) -> Result<Self, ImageFailure> {
        Ok(Self {
            bytes: index(image.bytes.len())?,
            spans: index(image.spans.len())?,
            origins: index(image.origins.len())?,
            types: index(image.types.len())?,
            type_children: index(image.type_children.len())?,
            kinds: index(image.kinds.len())?,
            parameters: index(image.parameters.len())?,
            quantifiers: index(image.quantifiers.len())?,
            method_catalogs: index(image.method_catalogs.len())?,
            source_methods: index(image.source_methods.len())?,
            method_variables: index(image.method_variables.len())?,
            inherited_parameters: index(image.inherited_parameters.len())?,
        })
    }

    fn validate(self, image: &PureImage) -> Result<(), ImageFailure> {
        let available = Self::seal(image)?;
        if self.bytes > available.bytes
            || self.spans > available.spans
            || self.origins > available.origins
            || self.types > available.types
            || self.type_children > available.type_children
            || self.kinds > available.kinds
            || self.parameters > available.parameters
            || self.quantifiers > available.quantifiers
            || self.method_catalogs > available.method_catalogs
            || self.source_methods > available.source_methods
            || self.method_variables > available.method_variables
            || self.inherited_parameters > available.inherited_parameters
        {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(())
    }
}

fn native_fact_table<T>(
    records: &[T],
    prefix: u32,
    executable: bool,
) -> Result<&[T], ImageFailure> {
    let prefix = records
        .get(..usize::try_from(prefix).map_err(|_| ImageFailure::InvalidRecord)?)
        .ok_or(ImageFailure::InvalidRecord)?;
    Ok(if executable { records } else { prefix })
}

#[derive(Debug, Default)]
pub(crate) struct PureImage {
    effect_dialect: bool,
    native_fact_prefixes: Option<NativeFactPrefixes>,
    kinds: Vec<KindRecord>,
    parameters: Vec<ParameterRecord>,
    quantifiers: Vec<QuantifierRecord>,
    nominal_parameters: Vec<NominalParameterRecord>,
    global_parameters: Vec<GlobalParameterRowRecord>,
    abstract_nominals: Vec<AbstractNominalRecord>,
    provenance: Vec<ProvenanceRecord>,
    provenance_children: Vec<u32>,
    provenance_views: Vec<ProvenanceViewRecord>,
    effects: Vec<EffectDeclarationRecord>,
    operations: Vec<EffectOperationRecord>,

    prepared_symbols: Vec<PreparedSymbolRecord>,
    prepared_libraries: Vec<PreparedLibraryRecord>,
    native_symbols: Vec<NativeSymbolRecord>,

    template_nodes: Vec<NodeRecord>,

    source_handlers: Vec<HandlerRecord>,
    source_clauses: Vec<ClauseRecord>,
    interface_owners: Vec<InterfaceOwnerRecord>,
    scope_parameters: Vec<u32>,
    method_catalogs: Vec<MethodCatalogRecord>,
    source_methods: Vec<MethodRecord>,
    inherited_parameters: Vec<InheritedParameterRecord>,
    method_arguments: Vec<u32>,
    method_variables: Vec<TypeVariableIdentity>,

    main_method_catalog: Option<u32>,
    source_method_evidence: Vec<u8>,
    source_method_anchors: Option<Slice>,

    interpretations: Vec<NativeInterpretationRecord>,
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

/// Paid merge passes over retained portable keys; values are borrowed or flat
/// records. Key comparison cannot walk Type/Row/provenance trees.
fn sort_image_records<T: Copy, K: Ord>(
    items: &mut [T],
    key: impl Fn(&T) -> K,
    work: &mut TypeWorkBudget,
) -> Result<(), ImageFailure> {
    let count = items.len();
    charge(work, count)?;
    if count < 2 {
        return Ok(());
    }
    let mut scratch = Vec::new();
    scratch
        .try_reserve_exact(count)
        .map_err(|_| ImageFailure::Resource)?;
    scratch.resize(count, items[0]);
    let mut width = 1usize;
    while width < count {
        charge(work, count.checked_mul(3).ok_or(ImageFailure::Resource)?)?;
        let mut start = 0usize;
        while start < count {
            let middle = start.saturating_add(width).min(count);
            let end = middle.saturating_add(width).min(count);
            let (mut left, mut right) = (start, middle);
            for output in &mut scratch[start..end] {
                if left < middle && (right == end || key(&items[left]) <= key(&items[right])) {
                    *output = items[left];
                    left += 1;
                } else {
                    *output = items[right];
                    right += 1;
                }
            }
            start = end;
        }
        items.copy_from_slice(&scratch);
        width = width.checked_mul(2).unwrap_or(count);
    }
    Ok(())
}

fn get<T>(records: &[T], slot: u32) -> Result<&T, ImageFailure> {
    records
        .get(usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?)
        .ok_or(ImageFailure::InvalidRecord)
}

struct Encoder<'a> {
    image: PureImage,
    structural: HashMap<StructuralKey, u32>,
    kind_records: HashMap<KindRecord, u32>,
    quantifier_vectors: HashMap<Box<[QuantifierRecord]>, Slice>,
    modules: HashMap<ModuleId, u32>,
    sources: HashMap<SourceId, u32>,
    binders: HashMap<BinderId, u32>,
    remapped: Vec<Option<u32>>,
    prepared_libraries:
        HashMap<*const crate::foreign::source_contract::PreparedForeignLibrary, u32>,
    native_symbols: HashMap<
        crate::types::OperationId,
        (
            *const crate::foreign::checked_source::CheckedForeignSymbol,
            u32,
        ),
    >,

    // Exact flat representation keys only. Every origin is still traversed
    // and depth checked; no validation or source correspondence is retained.
    origin_records: HashMap<OriginRecord, u32>,
    origin_spans: HashMap<Vec<SpanRecord>, Slice>,
    original_native_symbols: Vec<Arc<crate::foreign::checked_source::CheckedForeignSymbol>>,
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
    encode_program(
        program,
        provenance,
        work,
        false,
        |_| Ok(()),
        |encoder, kind| encoder.encode_node(kind),
    )
    .map(|encoder| encoder.image)
}

fn encode_program<'work, F: crate::core::dialect::CoreOperationFamily>(
    program: &crate::core::dialect::ValidatedCoreProgram<F>,
    provenance: &[(ModuleId, Arc<SourceFile>)],
    work: &'work mut TypeWorkBudget,
    effect_dialect: bool,
    prepare_originals: impl FnOnce(&mut Encoder<'_>) -> Result<(), ImageFailure>,
    mut encode_kind: impl FnMut(&mut Encoder<'_>, &F::Kind) -> Result<NodeTag, ImageFailure>,
) -> Result<Encoder<'work>, ImageFailure> {
    let registry = program.registry();
    let catalog = program.method_evidence();
    if !effect_dialect
        && (!catalog.methods().is_empty()
            || !catalog.lexical_owners().is_empty()
            || !catalog.occurrences().is_empty()
            || !program.method_evidence_anchors().is_empty())
    {
        return Err(ImageFailure::Unsupported(Unsupported::MethodEvidence));
    }
    let mut encoder = Encoder {
        image: PureImage {
            effect_dialect,
            ..PureImage::default()
        },
        structural: HashMap::new(),
        kind_records: HashMap::new(),
        quantifier_vectors: HashMap::new(),
        modules: HashMap::new(),
        sources: HashMap::new(),
        binders: HashMap::new(),
        remapped: Vec::new(),
        prepared_libraries: HashMap::new(),
        native_symbols: HashMap::new(),

        origin_records: HashMap::new(),
        origin_spans: HashMap::new(),
        original_native_symbols: Vec::new(),
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
            SourceRecord {
                role: if module.is_builtin_foreign() {
                    ModuleRoleRecord::BuiltinForeign
                } else if module.is_builtin_region_facade() {
                    ModuleRoleRecord::BuiltinRegionFacade
                } else if module.is_builtin_region() {
                    ModuleRoleRecord::BuiltinRegion
                } else if module.is_builtin_generic_cell() {
                    ModuleRoleRecord::BuiltinGenericCell
                } else if module.is_builtin_cell() {
                    ModuleRoleRecord::BuiltinCell
                } else if module.is_builtin_string() {
                    ModuleRoleRecord::BuiltinString
                } else if module.is_builtin_bytes() {
                    ModuleRoleRecord::BuiltinBytes
                } else {
                    ModuleRoleRecord::Ordinary
                },
                path,
                text,
            },
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
    if effect_dialect {
        encoder.encode_extended_registry(registry)?;
    }
    if effect_dialect {
        encoder.image.main_method_catalog = Some(encoder.encode_method_catalog(catalog)?);
    }
    prepare_originals(&mut encoder)?;
    charge(encoder.work, 13)?;
    encoder.image.native_fact_prefixes = Some(NativeFactPrefixes::seal(&encoder.image)?);
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
            let tag = encode_kind(&mut encoder, &expression.kind)?;
            let effects = if effect_dialect {
                Some(encoder.encode_structural(StructuralInput::Row(expression.effects()))?)
            } else {
                None
            };
            let slot = push(
                &mut encoder.image.nodes,
                NodeRecord {
                    effects,
                    tag,
                    ty,
                    origin,
                },
                encoder.work,
            )?;
            *encoder
                .remapped
                .get_mut(usize::try_from(id.value()).map_err(|_| ImageFailure::InvalidRecord)?)
                .ok_or(ImageFailure::InvalidRecord)? = Some(slot);
        } else {
            push(&mut pending, (id, true), encoder.work)?;
            let count = F::child_count(&expression.kind);
            charge(encoder.work, count)?;
            for child in (0..count).rev() {
                push(
                    &mut pending,
                    (
                        F::child_at(&expression.kind, child).ok_or(ImageFailure::InvalidRecord)?,
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
    if effect_dialect {
        encoder.image.source_method_anchors =
            Some(encoder.encode_source_method_anchors(catalog, program.method_evidence_anchors())?);
    }
    Ok(encoder)
}

impl Encoder<'_> {
    fn encode_cell_acquisition(
        &mut self,
        acquisition: crate::resolved::ResourceAcquisition,
    ) -> Result<CellAcquisitionRecord, ImageFailure> {
        let crate::resolved::ResourceMethods::Cell([read, write]) = acquisition.methods;
        if !acquisition.builtin.is_builtin_resource() {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        Ok(CellAcquisitionRecord {
            module: self.module(acquisition.builtin)?,
            identity: self.type_variable(acquisition.identity)?,
            handle: self.binder_id(acquisition.handle)?,
            provider_module: self.module(acquisition.provider.module())?,
            provider_local: acquisition.provider.declaration(),
            read: self.binder_id(read)?,
            write: self.binder_id(write)?,
            span: self.span(acquisition.span)?,
        })
    }

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
                    break self.intern_origin(OriginRecord::Source(span))?;
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
                OriginRecord::Related {
                    primary: result,
                    related: self
                        .intern_origin_spans(related.ok_or(ImageFailure::InvalidRecord)?)?,
                }
            };
            result = self.intern_origin(record)?;
        }
        Ok(result)
    }

    fn intern_origin(&mut self, record: OriginRecord) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        if let Some(slot) = self.origin_records.get(&record) {
            return Ok(*slot);
        }
        charge(self.work, 1)?;
        self.origin_records
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let slot = push(&mut self.image.origins, record, self.work)?;
        self.origin_records.insert(record, slot);
        Ok(slot)
    }

    fn intern_origin_spans(&mut self, spans: &[Span]) -> Result<Slice, ImageFailure> {
        charge(self.work, spans.len())?;
        let mut records = Vec::new();
        records
            .try_reserve_exact(spans.len())
            .map_err(|_| ImageFailure::Resource)?;
        for span in spans {
            records.push(self.span(*span)?);
        }
        // Pay the complete hash and possible equality traversal before lookup.
        charge(
            self.work,
            records
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ImageFailure::Resource)?,
        )?;
        if let Some(range) = self.origin_spans.get(&records) {
            return Ok(*range);
        }
        charge(self.work, 1)?;
        self.origin_spans
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let range = append(&mut self.image.spans, &records, self.work)?;
        self.origin_spans.insert(records, range);
        Ok(range)
    }

    fn encode_type(&mut self, ty: &Type) -> Result<u32, ImageFailure> {
        self.encode_structural(StructuralInput::Type(ty))
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
                PureValue::Integer(value) => {
                    if let Some(value) = value.value().to_i64() {
                        NodeTag::Integer(value)
                    } else {
                        if let Some(unsigned) = value.value().to_u64() {
                            NodeTag::UnsignedInteger(unsigned)
                        } else {
                            charge(
                                self.work,
                                usize::try_from(value.value().magnitude_byte_length())
                                    .map_err(|_| ImageFailure::Resource)?,
                            )?;
                            let (negative, bytes) = value.value().sign_magnitude();
                            NodeTag::IntegerMagnitude {
                                negative,
                                bytes: append(&mut self.image.bytes, &bytes, self.work)?,
                            }
                        }
                    }
                }
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
                PureValue::Intrinsic(value) => {
                    use crate::core::packed::Intrinsic;

                    let bytes = match value.operation() {
                        Intrinsic::BytesEmpty => Some(0),
                        Intrinsic::BytesAppendByte { appended, invalid } => {
                            let owner = NominalTypeId::new(value.module(), 0);
                            if appended != ConstructorId::new(owner, 0)
                                || invalid != ConstructorId::new(owner, 1)
                            {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            Some(1)
                        }
                        Intrinsic::BytesLength => Some(2),
                        Intrinsic::BytesEqual => Some(3),
                        Intrinsic::BytesAt { found, invalid } => {
                            let owner = NominalTypeId::new(value.module(), 1);
                            if found != ConstructorId::new(owner, 0)
                                || invalid != ConstructorId::new(owner, 1)
                            {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            Some(4)
                        }
                        _ => None,
                    };
                    let string = match value.operation() {
                        Intrinsic::StringByteLength => Some(0),
                        Intrinsic::StringToUtf8 => Some(1),
                        Intrinsic::StringEqual => Some(2),
                        Intrinsic::StringFromUtf8 { decoded, invalid } => {
                            let nominal = NominalTypeId::new(value.module(), 0);
                            if decoded != ConstructorId::new(nominal, 0)
                                || invalid != ConstructorId::new(nominal, 1)
                            {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            Some(3)
                        }
                        _ => None,
                    };
                    let address = match value.operation() {
                        Intrinsic::AddressNull => Some(0),
                        Intrinsic::AddressIsNull => Some(1),
                        Intrinsic::AddressEqual => Some(2),
                        _ => None,
                    };
                    if matches!(
                        value.operation(),
                        Intrinsic::RegionRequestBytes
                            | Intrinsic::RegionRequestAlignment
                            | Intrinsic::RegionFromBacking { .. }
                    ) {
                        if !value.module().is_builtin_region() {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        let (operation, owner, address_module) = match value.operation() {
                            Intrinsic::RegionRequestBytes => (0, None, None),
                            Intrinsic::RegionRequestAlignment => (1, None, None),
                            Intrinsic::RegionFromBacking {
                                owner,
                                address_module,
                            } => {
                                if !address_module.is_builtin_foreign() {
                                    return Err(ImageFailure::InvalidRecord);
                                }
                                (
                                    2,
                                    Some(self.type_variable(owner)?),
                                    Some(self.module(address_module)?),
                                )
                            }
                            _ => return Err(ImageFailure::InvalidRecord),
                        };
                        NodeTag::RegionBinding {
                            module: self.module(value.module())?,
                            operation,
                            owner,
                            address_module,
                        }
                    } else if let Intrinsic::RegionHostAllocate {
                        owner,
                        configuration,
                    }
                    | Intrinsic::RegionHostRelease {
                        owner,
                        configuration,
                    } = value.operation()
                    {
                        if !value.module().is_builtin_region()
                            || configuration != crate::core::region::HostRegionConfiguration::System
                        {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        NodeTag::RegionHost {
                            module: self.module(value.module())?,
                            owner: self.type_variable(owner)?,
                            release: matches!(
                                value.operation(),
                                Intrinsic::RegionHostRelease { .. }
                            ),
                        }
                    } else if let Some(operation) = address {
                        if !value.module().is_builtin_foreign() {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        NodeTag::AddressIntrinsic {
                            module: self.module(value.module())?,
                            operation,
                        }
                    } else if let Some(operation) = bytes {
                        if !value.module().is_builtin_bytes() {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        NodeTag::BytesIntrinsic {
                            module: self.module(value.module())?,
                            operation,
                        }
                    } else if let Some(operation) = string {
                        if !value.module().is_builtin_string() {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        NodeTag::StringIntrinsic {
                            module: self.module(value.module())?,
                            operation,
                        }
                    } else {
                        return Err(ImageFailure::Unsupported(Unsupported::Intrinsic));
                    }
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
                PureComputation::TypeAbstraction(abstraction) if self.image.effect_dialect => {
                    let parameters = self.encode_quantifiers(abstraction.parameters())?;
                    NodeTag::TypeAbstraction {
                        parameters,
                        body: self.node(abstraction.body())?,
                    }
                }
                PureComputation::TypeApplication(application) if self.image.effect_dialect => {
                    let mut type_roots = Vec::new();
                    for argument in application.arguments() {
                        let argument = self.encode_type(argument)?;
                        push(&mut type_roots, argument, self.work)?;
                    }
                    let arguments = append(&mut self.image.type_children, &type_roots, self.work)?;
                    let mut row_roots = Vec::new();
                    for row in application.row_arguments() {
                        let row = self.encode_structural(StructuralInput::Row(row))?;
                        push(&mut row_roots, row, self.work)?;
                    }
                    NodeTag::TypeApplication {
                        function: self.node(application.function())?,
                        arguments,
                        row_arguments: append(
                            &mut self.image.type_children,
                            &row_roots,
                            self.work,
                        )?,
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

// The build image restores one coordinate arena. Generated correspondence
// facts borrow it later; they never reconstruct or reopen sources a second time.
enum CoordinateStorage<'a, T> {
    Owned(Vec<T>),
    Borrowed(&'a [T]),
}
impl<T> std::ops::Deref for CoordinateStorage<'_, T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            Self::Owned(values) => values,
            Self::Borrowed(values) => values,
        }
    }
}
impl<T> CoordinateStorage<'_, T> {
    fn push(&mut self, value: T, work: &mut TypeWorkBudget) -> Result<(), ImageFailure> {
        let Self::Owned(values) = self else {
            return Err(ImageFailure::InvalidRecord);
        };
        push(values, value, work)?;
        Ok(())
    }
    fn into_owned(self) -> Result<Vec<T>, ImageFailure> {
        match self {
            Self::Owned(values) => Ok(values),
            Self::Borrowed(_) => Err(ImageFailure::InvalidRecord),
        }
    }
}

struct Decoder<'a> {
    image: &'a PureImage,
    expected_fact_prefixes: Option<NativeFactPrefixes>,
    sources: CoordinateStorage<'a, SourceFile>,
    modules: CoordinateStorage<'a, ModuleId>,
    // Representation sharing within this immutable image/coordinate/prefix
    // context only. No registry or per-forest validation result is retained.
    source_declaration_catalogs: HashMap<u32, Arc<crate::core::dialect::MethodEvidenceCatalog>>,
    // Passive owned Type values only, within this immutable image and exact
    // append-only coordinate context. Prefix-bounded expectation reads never
    // consult or populate this table. No kind/registry/Core proof is cached.
    decoded_types: HashMap<(u32, usize, usize), DecodedType>,
    // Canonical Row data shares the same cold-domain and coordinate rules.
    // Each caller receives a fresh full-kinded clone, never an admission proof.
    decoded_rows: HashMap<(u32, usize, usize), DecodedRow>,
    work: &'a mut TypeWorkBudget,
}

struct DecodedRow {
    value: crate::types::EffectRow,
    depth: usize,
}

struct DecodedType {
    value: IterativeTypeOwner,
    // Maximum additional Core structural depth reached during the same raw
    // reconstruction. A reused subtree must fit its current enclosing depth.
    depth: usize,
}

// A private layout marker for the matching compiler/runtime only. Neither the
// embedded byte sequence nor its numeric tags promise compatibility.
const PRIVATE_MAGIC: &[u8] = b"ash-private-program\x17";

enum WireOutput<'a> {
    Encoded(Vec<u8>),
    Expected { bytes: &'a [u8], offset: usize },
}

struct WireWriter<'a> {
    output: WireOutput<'a>,
    work: &'a mut TypeWorkBudget,
}

impl WireWriter<'_> {
    fn bytes(&mut self, bytes: &[u8]) -> Result<(), ImageFailure> {
        match &mut self.output {
            WireOutput::Encoded(encoded) => {
                append(encoded, bytes, self.work)?;
            }
            WireOutput::Expected {
                bytes: expected,
                offset,
            } => {
                // Compare the same canonical wire chunks without allocating a
                // duplicate encoding. Charge before inspecting their bytes.
                charge(self.work, bytes.len())?;
                let end = offset
                    .checked_add(bytes.len())
                    .ok_or(ImageFailure::Resource)?;
                index(end)?;
                if expected.get(*offset..end) != Some(bytes) {
                    return Err(ImageFailure::InvalidRecord);
                }
                *offset = end;
            }
        }
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
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        // Private indices/counts use one canonical unsigned base-128 spelling.
        // Native scalar values retain their separate fixed-width encoding.
        let mut bytes = [0; 5];
        let mut value = *self;
        let mut length = 0;
        loop {
            let mut byte = (value & 127) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 128;
            }
            bytes[length] = byte;
            length += 1;
            if value == 0 {
                break;
            }
        }
        writer.bytes(&bytes[..length])
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        let mut value = 0;
        for group in 0..5 {
            let byte = u8::read(reader)?;
            if group == 4 && byte > 15 {
                return Err(ImageFailure::InvalidEncoding);
            }
            value |= u32::from(byte & 127) << (group * 7);
            if byte & 128 == 0 {
                if group != 0 && byte == 0 {
                    return Err(ImageFailure::InvalidEncoding);
                }
                return Ok(value);
            }
        }
        Err(ImageFailure::InvalidEncoding)
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

const fn field_wire_minimum<Owner, Field: Wire>(_: fn(&Owner) -> &Field) -> usize {
    Field::MINIMUM
}

macro_rules! wire_struct {
    ($name:ident, $($field:ident),+ $(,)?) => {
        impl Wire for $name {
            // Derive the allocation precheck from the actual field codecs,
            // so compact indices cannot leave a stale fixed-width bound.
            const MINIMUM: usize = 0 $(+ $crate::build::image::field_wire_minimum::<Self, _>(|record| &record.$field))+;
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

wire_struct!(Slice, start, len);
wire_struct!(
    NativeFactPrefixes,
    bytes,
    spans,
    origins,
    types,
    type_children,
    kinds,
    parameters,
    quantifiers,
    method_catalogs,
    source_methods,
    method_variables,
    inherited_parameters,
);
wire_struct!(SourceRecord, role, path, text);
wire_struct!(ProvenanceViewRecord, nodes, children, root);
wire_struct!(SpanRecord, source, start, end);
wire_struct!(NominalId, module, local);
wire_struct!(ConstructorIdentity, owner, local);
wire_struct!(TypeRecord, tag, children);
wire_struct!(BinderRecord, id, ty, origin);
wire_struct!(
    CellAcquisitionRecord,
    module,
    identity,
    handle,
    provider_module,
    provider_local,
    read,
    write,
    span
);
wire_struct!(PatternRecord, tag, children, ty, origin);
wire_struct!(ArmRecord, pattern, body, origin);
wire_struct!(RecursiveMemberRecord, binder, initializer);
wire_struct!(NodeRecord, effects, tag, ty, origin);
wire_struct!(NominalRecord, id, spelling, constructors, origin);
wire_struct!(ConstructorRecord, id, spelling, payload, origin);

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
    const MINIMUM: usize = 1 + u32::MINIMUM + u8::MINIMUM;
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
    const MINIMUM: usize = 1 + u32::MINIMUM;
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
        match self {
            Self::Resource(id) => {
                16u8.write(writer)?;
                id.write(writer)
            }
            Self::Int => 0u8.write(writer),
            Self::Bool => 1u8.write(writer),
            Self::Unit => 2u8.write(writer),
            Self::Bytes => 3u8.write(writer),
            Self::String => 4u8.write(writer),
            Self::Nominal(id) => {
                5u8.write(writer)?;
                id.write(writer)
            }
            Self::Function => 6u8.write(writer),
            Self::Tuple => 7u8.write(writer),
            Self::Variable(id) => {
                8u8.write(writer)?;
                id.write(writer)
            }
            Self::Application => 9u8.write(writer),
            Self::Forall { parameters } => {
                10u8.write(writer)?;
                parameters.write(writer)
            }
            Self::EffectfulFunction => 11u8.write(writer),
            Self::ArgumentType => 12u8.write(writer),
            Self::ArgumentRow => 13u8.write(writer),
            Self::Instance(id) => {
                14u8.write(writer)?;
                id.write(writer)
            }

            Self::Row { known, tail } => {
                15u8.write(writer)?;
                known.write(writer)?;
                tail.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(match u8::read(reader)? {
            16 => Self::Resource(Wire::read(reader)?),
            0 => Self::Int,
            1 => Self::Bool,
            2 => Self::Unit,
            3 => Self::Bytes,
            4 => Self::String,
            5 => Self::Nominal(Wire::read(reader)?),
            6 => Self::Function,
            7 => Self::Tuple,
            8 => Self::Variable(Wire::read(reader)?),
            9 => Self::Application,
            10 => Self::Forall {
                parameters: Wire::read(reader)?,
            },
            11 => Self::EffectfulFunction,
            12 => Self::ArgumentType,
            13 => Self::ArgumentRow,
            14 => Self::Instance(Wire::read(reader)?),
            15 => Self::Row {
                known: Wire::read(reader)?,
                tail: Wire::read(reader)?,
            },
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
            Self::IntegerMagnitude { negative, bytes } => {
                37u8.write(writer)?;
                negative.write(writer)?;
                bytes.write(writer)
            }
            Self::RegionBuffer {
                api,
                context,
                operand,
                right,
                source,
                module,
                operation,
                bytes,
            } => {
                36u8.write(writer)?;
                api.write(writer)?;
                context.write(writer)?;
                operand.write(writer)?;
                right.write(writer)?;
                source.write(writer)?;
                module.write(writer)?;
                operation.write(writer)?;
                bytes.write(writer)
            }
            Self::RegionValueRequest { api, fields } => {
                34u8.write(writer)?;
                api.write(writer)?;
                fields.write(writer)
            }
            Self::RegionTuple {
                constructor,
                api,
                context,
                storage,
                fields,
            } => {
                35u8.write(writer)?;
                constructor.write(writer)?;
                api.write(writer)?;
                context.write(writer)?;
                storage.write(writer)?;
                fields.write(writer)
            }
            Self::RegionBinding {
                module,
                operation,
                owner,
                address_module,
            } => {
                33u8.write(writer)?;
                module.write(writer)?;
                operation.write(writer)?;
                owner.write(writer)?;
                address_module.write(writer)
            }
            Self::Region {
                entry,
                api,
                identity,
                access,
                preceding,
                provider,
                body,
            } => {
                30u8.write(writer)?;
                entry.write(writer)?;
                api.write(writer)?;
                identity.write(writer)?;
                access.write(writer)?;
                preceding.write(writer)?;
                provider.write(writer)?;
                body.write(writer)
            }
            Self::RegionAllocate {
                api,
                context,
                request,
            } => {
                31u8.write(writer)?;
                api.write(writer)?;
                context.write(writer)?;
                request.write(writer)
            }
            Self::RegionHost {
                module,
                owner,
                release,
            } => {
                32u8.write(writer)?;
                module.write(writer)?;
                owner.write(writer)?;
                release.write(writer)
            }
            Self::AddressIntrinsic { module, operation } => {
                29u8.write(writer)?;
                module.write(writer)?;
                operation.write(writer)
            }
            Self::BytesIntrinsic { module, operation } => {
                28u8.write(writer)?;
                module.write(writer)?;
                operation.write(writer)
            }
            Self::StringIntrinsic { module, operation } => {
                26u8.write(writer)?;
                module.write(writer)?;
                operation.write(writer)
            }
            Self::CellScope {
                acquisition,
                handle,
                initializer,
                body,
            } => {
                23u8.write(writer)?;
                acquisition.write(writer)?;
                handle.write(writer)?;
                initializer.write(writer)?;
                body.write(writer)
            }
            Self::Cleanup {
                callback,
                body,
                action,
                span,
                action_span,
            } => {
                24u8.write(writer)?;
                callback.write(writer)?;
                body.write(writer)?;
                action.write(writer)?;
                span.write(writer)?;
                action_span.write(writer)
            }
            Self::Registration {
                handler,
                callback,
                body,
                span,
            } => {
                25u8.write(writer)?;
                handler.write(writer)?;
                callback.write(writer)?;
                body.write(writer)?;
                span.write(writer)
            }
            Self::Handler(slot) => {
                17u8.write(writer)?;
                slot.write(writer)
            }
            Self::Resume {
                handler,
                owner,
                available,
                value,
            } => {
                18u8.write(writer)?;
                handler.write(writer)?;
                owner.write(writer)?;
                available.write(writer)?;
                value.write(writer)
            }
            Self::Discard {
                handler,
                owner,
                available,
            } => {
                19u8.write(writer)?;
                handler.write(writer)?;
                owner.write(writer)?;
                available.write(writer)
            }

            Self::Request {
                effect,
                operation,
                operand,
            } => {
                13u8.write(writer)?;
                effect.write(writer)?;
                operation.write(writer)?;
                operand.write(writer)
            }
            Self::NativeInterpret {
                body,
                interpretations,
            } => {
                14u8.write(writer)?;
                body.write(writer)?;
                interpretations.write(writer)
            }
            Self::TypeAbstraction { parameters, body } => {
                15u8.write(writer)?;
                parameters.write(writer)?;
                body.write(writer)
            }
            Self::TypeApplication {
                function,
                arguments,
                row_arguments,
            } => {
                16u8.write(writer)?;
                function.write(writer)?;
                arguments.write(writer)?;
                row_arguments.write(writer)
            }
            Self::Unit => 0u8.write(writer),
            Self::Integer(value) => {
                1u8.write(writer)?;
                value.write(writer)
            }
            Self::UnsignedInteger(value) => {
                22u8.write(writer)?;
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
            37 => Self::IntegerMagnitude {
                negative: Wire::read(reader)?,
                bytes: Wire::read(reader)?,
            },
            36 => Self::RegionBuffer {
                api: Wire::read(reader)?,
                context: Wire::read(reader)?,
                operand: Wire::read(reader)?,
                right: Wire::read(reader)?,
                source: Wire::read(reader)?,
                module: Wire::read(reader)?,
                operation: Wire::read(reader)?,
                bytes: Wire::read(reader)?,
            },
            34 => Self::RegionValueRequest {
                api: Wire::read(reader)?,
                fields: Wire::read(reader)?,
            },
            35 => Self::RegionTuple {
                constructor: Wire::read(reader)?,
                api: Wire::read(reader)?,
                context: Wire::read(reader)?,
                storage: Wire::read(reader)?,
                fields: Wire::read(reader)?,
            },
            33 => Self::RegionBinding {
                module: Wire::read(reader)?,
                operation: Wire::read(reader)?,
                owner: Wire::read(reader)?,
                address_module: Wire::read(reader)?,
            },
            30 => Self::Region {
                entry: Wire::read(reader)?,
                api: Wire::read(reader)?,
                identity: Wire::read(reader)?,
                access: Wire::read(reader)?,
                preceding: Wire::read(reader)?,
                provider: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            31 => Self::RegionAllocate {
                api: Wire::read(reader)?,
                context: Wire::read(reader)?,
                request: Wire::read(reader)?,
            },
            32 => Self::RegionHost {
                module: Wire::read(reader)?,
                owner: Wire::read(reader)?,
                release: Wire::read(reader)?,
            },
            26 => Self::StringIntrinsic {
                module: Wire::read(reader)?,
                operation: Wire::read(reader)?,
            },
            29 => Self::AddressIntrinsic {
                module: Wire::read(reader)?,
                operation: Wire::read(reader)?,
            },
            28 => Self::BytesIntrinsic {
                module: Wire::read(reader)?,
                operation: Wire::read(reader)?,
            },
            23 => Self::CellScope {
                acquisition: Wire::read(reader)?,
                handle: Wire::read(reader)?,
                initializer: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            24 => Self::Cleanup {
                callback: Wire::read(reader)?,
                body: Wire::read(reader)?,
                action: Wire::read(reader)?,
                span: Wire::read(reader)?,
                action_span: Wire::read(reader)?,
            },
            25 => Self::Registration {
                handler: Wire::read(reader)?,
                callback: Wire::read(reader)?,
                body: Wire::read(reader)?,
                span: Wire::read(reader)?,
            },
            17 => Self::Handler(Wire::read(reader)?),
            18 => Self::Resume {
                handler: Wire::read(reader)?,
                owner: Wire::read(reader)?,
                available: Wire::read(reader)?,
                value: Wire::read(reader)?,
            },
            19 => Self::Discard {
                handler: Wire::read(reader)?,
                owner: Wire::read(reader)?,
                available: Wire::read(reader)?,
            },

            0 => Self::Unit,
            1 => Self::Integer(Wire::read(reader)?),
            22 => Self::UnsignedInteger(Wire::read(reader)?),
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
            13 => Self::Request {
                effect: Wire::read(reader)?,
                operation: Wire::read(reader)?,
                operand: Wire::read(reader)?,
            },
            14 => Self::NativeInterpret {
                body: Wire::read(reader)?,
                interpretations: Wire::read(reader)?,
            },
            15 => Self::TypeAbstraction {
                parameters: Wire::read(reader)?,
                body: Wire::read(reader)?,
            },
            16 => Self::TypeApplication {
                function: Wire::read(reader)?,
                arguments: Wire::read(reader)?,
                row_arguments: Wire::read(reader)?,
            },
            _ => return Err(ImageFailure::InvalidEncoding),
        })
    }
}

impl PureImage {
    pub(crate) fn encode_bytes(&self, work: &mut TypeWorkBudget) -> Result<Vec<u8>, ImageFailure> {
        self.encode_selected_tables(work, true)
    }

    /// Independently embedded source/foreign facts, through the same wire codec.
    /// Core executable tables are absent; indices into fact tables stay exact.
    pub(crate) fn encode_native_expectations(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<u8>, ImageFailure> {
        self.encode_selected_tables(work, false)
    }

    fn encode_selected_tables(
        &self,
        work: &mut TypeWorkBudget,
        executable: bool,
    ) -> Result<Vec<u8>, ImageFailure> {
        let mut writer = WireWriter {
            output: WireOutput::Encoded(Vec::new()),
            work,
        };
        self.write_selected_tables(&mut writer, executable)?;
        match writer.output {
            WireOutput::Encoded(bytes) => Ok(bytes),
            WireOutput::Expected { .. } => Err(ImageFailure::InvalidRecord),
        }
    }

    fn compare_native_expectations(
        &self,
        expected: &[u8],
        work: &mut TypeWorkBudget,
    ) -> Result<(), ImageFailure> {
        let mut writer = WireWriter {
            output: WireOutput::Expected {
                bytes: expected,
                offset: 0,
            },
            work,
        };
        self.write_selected_tables(&mut writer, false)?;
        // Matching every emitted chunk also requires no trailing expected data.
        charge(writer.work, 1)?;
        match writer.output {
            WireOutput::Expected { bytes, offset } if offset == bytes.len() => Ok(()),
            _ => Err(ImageFailure::InvalidRecord),
        }
    }

    fn write_selected_tables(
        &self,
        writer: &mut WireWriter<'_>,
        executable: bool,
    ) -> Result<(), ImageFailure> {
        writer.bytes(PRIVATE_MAGIC)?;
        self.effect_dialect.write(writer)?;
        let prefixes = self
            .native_fact_prefixes
            .ok_or(ImageFailure::InvalidRecord)?;
        prefixes.write(writer)?;
        let bytes = native_fact_table(&self.bytes, prefixes.bytes, executable)?;
        index(bytes.len())?.write(writer)?;
        writer.bytes(bytes)?;
        writer.table(&self.sources)?;
        writer.table(native_fact_table(&self.spans, prefixes.spans, executable)?)?;
        writer.table(native_fact_table(
            &self.origins,
            prefixes.origins,
            executable,
        )?)?;
        writer.table(native_fact_table(&self.types, prefixes.types, executable)?)?;
        writer.table(native_fact_table(
            &self.type_children,
            prefixes.type_children,
            executable,
        )?)?;
        writer.table(if executable { &self.binders } else { &[] })?;
        writer.table(if executable { &self.patterns } else { &[] })?;
        writer.table(if executable {
            &self.pattern_children
        } else {
            &[]
        })?;
        writer.table(if executable { &self.arms } else { &[] })?;
        writer.table(if executable {
            &self.recursive_members
        } else {
            &[]
        })?;
        writer.table(if executable { &self.nodes } else { &[] })?;
        writer.table(if executable { &self.node_children } else { &[] })?;
        writer.table(&self.nominals)?;
        writer.table(&self.constructors)?;
        writer.table(&self.nominal_constructors)?;
        writer.table(native_fact_table(&self.kinds, prefixes.kinds, executable)?)?;
        writer.table(native_fact_table(
            &self.parameters,
            prefixes.parameters,
            executable,
        )?)?;
        writer.table(native_fact_table(
            &self.quantifiers,
            prefixes.quantifiers,
            executable,
        )?)?;
        writer.table(&self.nominal_parameters)?;
        writer.table(&self.global_parameters)?;
        writer.table(&self.abstract_nominals)?;
        writer.table(&self.provenance)?;
        writer.table(&self.provenance_children)?;
        writer.table(&self.provenance_views)?;
        writer.table(&self.effects)?;
        writer.table(&self.operations)?;

        writer.table(&self.prepared_symbols)?;
        writer.table(&self.prepared_libraries)?;
        writer.table(&self.native_symbols)?;

        writer.table(&self.source_handlers)?;
        writer.table(&self.source_clauses)?;
        writer.table(&self.interface_owners)?;
        writer.table(&self.scope_parameters)?;

        writer.table(native_fact_table(
            &self.method_catalogs,
            prefixes.method_catalogs,
            executable,
        )?)?;
        writer.table(native_fact_table(
            &self.source_methods,
            prefixes.source_methods,
            executable,
        )?)?;
        writer.table(native_fact_table(
            &self.method_variables,
            prefixes.method_variables,
            executable,
        )?)?;
        writer.table(native_fact_table(
            &self.inherited_parameters,
            prefixes.inherited_parameters,
            executable,
        )?)?;
        writer.table(&self.method_arguments)?;
        self.main_method_catalog.write(writer)?;
        writer.table(if executable {
            &self.source_method_evidence
        } else {
            &[]
        })?;
        (if executable {
            self.source_method_anchors
        } else {
            None
        })
        .write(writer)?;
        writer.table(if executable {
            &self.template_nodes
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.interpretations
        } else {
            &[]
        })?;
        (if executable { self.root } else { 0 }).write(writer)?;
        Ok(())
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
        let effect_dialect = bool::read(&mut reader)?;
        let image = Self {
            effect_dialect,
            native_fact_prefixes: Some(NativeFactPrefixes::read(&mut reader)?),
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
            kinds: reader.table()?,
            parameters: reader.table()?,
            quantifiers: reader.table()?,
            nominal_parameters: reader.table()?,
            global_parameters: reader.table()?,
            abstract_nominals: reader.table()?,
            provenance: reader.table()?,
            provenance_children: reader.table()?,
            provenance_views: reader.table()?,
            effects: reader.table()?,
            operations: reader.table()?,

            prepared_symbols: reader.table()?,
            prepared_libraries: reader.table()?,
            native_symbols: reader.table()?,

            source_handlers: reader.table()?,
            source_clauses: reader.table()?,
            interface_owners: reader.table()?,
            scope_parameters: reader.table()?,

            method_catalogs: reader.table()?,
            source_methods: reader.table()?,
            method_variables: reader.table()?,
            inherited_parameters: reader.table()?,
            method_arguments: reader.table()?,
            main_method_catalog: Wire::read(&mut reader)?,
            source_method_evidence: reader.byte_table()?,
            source_method_anchors: Wire::read(&mut reader)?,

            template_nodes: reader.table()?,

            interpretations: reader.table()?,
            root: u32::read(&mut reader)?,
        };
        charge(reader.work, 1)?;
        if reader.offset != bytes.len() {
            return Err(ImageFailure::InvalidEncoding);
        }
        charge(reader.work, 13)?;
        image
            .native_fact_prefixes
            .ok_or(ImageFailure::InvalidRecord)?
            .validate(&image)?;
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
        // Pure images retain only canonical inert Foreign declarations after
        // defining-source and complete registry reconstruction below. Effect
        // operations and polymorphic applications remain outside this profile.
        charge(work, 1)?;
        if self.effect_dialect
            || !self.abstract_nominals.is_empty()
            || !self.operations.is_empty()
            || !self.prepared_symbols.is_empty()
            || !self.prepared_libraries.is_empty()
            || !self.native_symbols.is_empty()
            || !self.interface_owners.is_empty()
            || !self.scope_parameters.is_empty()
            || !self.method_catalogs.is_empty()
            || !self.source_methods.is_empty()
            || !self.method_variables.is_empty()
            || !self.inherited_parameters.is_empty()
            || self.main_method_catalog.is_some()
            || !self.source_method_evidence.is_empty()
            || self.source_method_anchors.is_some()
            || !self.template_nodes.is_empty()
            || !self.interpretations.is_empty()
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        let mut decoder = Decoder {
            image: self,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Owned(Vec::new()),
            modules: CoordinateStorage::Owned(Vec::new()),
            work,
        };
        if self.sources.is_empty() {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut seen_common = false;
        let mut seen_string = false;
        let mut seen_bytes = false;
        let mut seen_region = false;
        let mut seen_region_facade = false;
        for record in &self.sources {
            charge(decoder.work, 1)?;
            let path = decoder.text(record.path)?;
            let text = decoder.text(record.text)?;
            let source = SourceFile::new_with_budget(path, text, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            let role = match record.role {
                ModuleRoleRecord::Ordinary => crate::module::ImageModuleRole::Ordinary,
                ModuleRoleRecord::BuiltinRegionFacade => {
                    if std::mem::replace(&mut seen_region_facade, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinRegionFacade
                }
                ModuleRoleRecord::BuiltinRegion => {
                    if std::mem::replace(&mut seen_region, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinRegion
                }
                ModuleRoleRecord::BuiltinString => {
                    if std::mem::replace(&mut seen_string, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinString
                }
                ModuleRoleRecord::BuiltinBytes => {
                    if std::mem::replace(&mut seen_bytes, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinBytes
                }
                ModuleRoleRecord::BuiltinCell | ModuleRoleRecord::BuiltinGenericCell => {
                    return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                }
                ModuleRoleRecord::BuiltinForeign => {
                    if std::mem::replace(&mut seen_common, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinForeign
                }
            };
            let module = crate::module::restore_image_module(&source, role, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            decoder.sources.push(source, decoder.work)?;
            decoder.modules.push(module, decoder.work)?;
        }
        let registry = if seen_common {
            decoder.extended_registry()?.registry
        } else {
            if !self.effects.is_empty()
                || !self.kinds.is_empty()
                || !self.parameters.is_empty()
                || !self.nominal_parameters.is_empty()
                || !self.quantifiers.is_empty()
                || !self.global_parameters.is_empty()
                || !self.provenance.is_empty()
                || !self.provenance_children.is_empty()
                || !self.provenance_views.is_empty()
            {
                return Err(ImageFailure::InvalidRecord);
            }
            decoder.registry()?
        };
        if !registry
            .monomorphic_image_subset(decoder.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
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
        builder.reserve_image_binders(&binder_ids, decoder.work)?;
        let mut nodes = Vec::new();
        charge(decoder.work, self.nodes.len())?;
        nodes
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| ImageFailure::Resource)?;
        for (slot, record) in self.nodes.iter().enumerate() {
            charge(decoder.work, 1)?;
            if record.effects.is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
            let ty = decoder.ty(record.ty)?;
            let origin = decoder.origin(record.origin)?;
            let node = decoder.node(&mut builder, &nodes, record.tag, ty, origin)?;
            if nodes.len() != slot {
                return Err(ImageFailure::InvalidRecord);
            }
            nodes.push(node);
        }
        let root = *get(&nodes, self.root)?;
        let unchecked = builder.finish_image(root, decoder.work)?;
        let mut sources = Vec::new();
        let mut module_sources = Vec::new();
        for (module, source) in decoder.modules.iter().zip(decoder.sources.iter()) {
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
    /// Expected declarations can borrow the authenticated construction tables,
    /// but can never read executable suffix records as original fact metadata.
    fn fact_table<'records, T>(
        &self,
        records: &'records [T],
        prefix: fn(NativeFactPrefixes) -> u32,
    ) -> Result<&'records [T], ImageFailure> {
        match self.expected_fact_prefixes {
            Some(prefixes) => native_fact_table(records, prefix(prefixes), false),
            None => Ok(records),
        }
    }

    fn text(&mut self, range: Slice) -> Result<String, ImageFailure> {
        let bytes = range.get(self.fact_table(&self.image.bytes, |p| p.bytes)?)?;
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
            let record = *get(
                self.fact_table(&self.image.origins, |p| p.origins)?,
                current,
            )?;
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
                    for record in related.get(self.fact_table(&self.image.spans, |p| p.spans)?)? {
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
        if self.expected_fact_prefixes.is_some() {
            return self.structural(root)?.ty();
        }
        // Coordinates are append-only during module restoration. Including
        // both lengths prevents a value decoded in a partial context from
        // becoming the representation for a later context.
        let key = (root, self.sources.len(), self.modules.len());
        charge(self.work, 1)?;
        if let Some(ty) = self.decoded_types.get(&key) {
            return crate::types::clone_type_with_budget(&ty.value, self.work)
                .map(IterativeTypeOwner::new)
                .map_err(|()| ImageFailure::Resource);
        }
        let (ty, depth) = self.structural_with_depth(root)?;
        let ty = ty.ty()?;
        // Admit the retained table entry and the caller's independent owned
        // copy before publishing either. All partial trees have iterative Drop.
        charge(self.work, 1)?;
        self.decoded_types
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let copied = crate::types::clone_type_with_budget(&ty, self.work)
            .map(IterativeTypeOwner::new)
            .map_err(|()| ImageFailure::Resource)?;
        self.decoded_types
            .insert(key, DecodedType { value: ty, depth });
        Ok(copied)
    }

    // Pure decoded representation only. Prefix-bounded facts and pending-row
    // domains always reconstruct cold, just as they do for decoded Type values.
    fn row(&mut self, root: u32) -> Result<crate::types::EffectRow, ImageFailure> {
        if self.expected_fact_prefixes.is_some() {
            return self.structural(root)?.row();
        }
        let key = (root, self.sources.len(), self.modules.len());
        charge(self.work, 1)?;
        if let Some(row) = self.decoded_rows.get(&key) {
            return crate::types::clone_effect_row_with_budget(&row.value, self.work)
                .map_err(|()| ImageFailure::Resource);
        }
        let (value, depth) = self.structural_with_depth(root)?;
        let value = value.row()?;
        charge(self.work, 1)?;
        self.decoded_rows
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let caller = crate::types::clone_effect_row_with_budget(&value, self.work)
            .map_err(|()| ImageFailure::Resource)?;
        self.decoded_rows.insert(key, DecodedRow { value, depth });
        Ok(caller)
    }

    fn binder<F: crate::core::dialect::CoreOperationFamily>(
        &mut self,
        builder: &mut CoreBuilder<F>,
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

    fn pattern<F: crate::core::dialect::CoreOperationFamily>(
        &mut self,
        builder: &mut CoreBuilder<F>,
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

    fn node<F: crate::core::dialect::CoreOperationFamily>(
        &mut self,
        builder: &mut CoreBuilder<F>,
        nodes: &[NodeId],
        record: NodeTag,
        ty: IterativeTypeOwner,
        origin: OriginOwner,
    ) -> Result<NodeId, ImageFailure> {
        let node = match record {
            NodeTag::Region { .. }
            | NodeTag::RegionValueRequest { .. }
            | NodeTag::RegionTuple { .. }
            | NodeTag::RegionBuffer { .. }
            | NodeTag::RegionAllocate { .. }
            | NodeTag::CellScope { .. }
            | NodeTag::Cleanup { .. }
            | NodeTag::Registration { .. }
            | NodeTag::Handler(_)
            | NodeTag::Resume { .. }
            | NodeTag::Discard { .. }
            | NodeTag::Request { .. }
            | NodeTag::NativeInterpret { .. } => {
                return Err(ImageFailure::Unsupported(Unsupported::EffectOperation));
            }

            NodeTag::TypeAbstraction { .. } | NodeTag::TypeApplication { .. } => {
                return Err(ImageFailure::Unsupported(Unsupported::ErasedTypeOperation));
            }
            NodeTag::RegionBinding {
                module,
                operation,
                owner,
                address_module,
            } => {
                let module = *get(&self.modules, module)?;
                if !module.is_builtin_region() {
                    return Err(ImageFailure::InvalidRecord);
                }
                use crate::core::packed::Intrinsic;
                let operation = match (operation, owner, address_module) {
                    (0, None, None) => Intrinsic::RegionRequestBytes,
                    (1, None, None) => Intrinsic::RegionRequestAlignment,
                    (2, Some(owner), Some(address_module)) => Intrinsic::RegionFromBacking {
                        owner: self.type_variable(owner)?,
                        address_module: *get(&self.modules, address_module)?,
                    },
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                if matches!(operation, Intrinsic::RegionFromBacking { address_module, .. } if !address_module.is_builtin_foreign())
                {
                    return Err(ImageFailure::InvalidRecord);
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }
            NodeTag::RegionHost {
                module,
                owner,
                release,
            } => {
                let module = *get(&self.modules, module)?;
                if !module.is_builtin_region() {
                    return Err(ImageFailure::InvalidRecord);
                }
                let owner = self.type_variable(owner)?;
                let configuration = crate::core::region::HostRegionConfiguration::System;
                let operation = if release {
                    crate::core::packed::Intrinsic::RegionHostRelease {
                        owner,
                        configuration,
                    }
                } else {
                    crate::core::packed::Intrinsic::RegionHostAllocate {
                        owner,
                        configuration,
                    }
                };
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }
            NodeTag::StringIntrinsic { module, operation } => {
                let module = *get(&self.modules, module)?;
                if !module.is_builtin_string() {
                    return Err(ImageFailure::InvalidRecord);
                }
                use crate::core::packed::Intrinsic;
                let operation = match operation {
                    0 => Intrinsic::StringByteLength,
                    1 => Intrinsic::StringToUtf8,
                    2 => Intrinsic::StringEqual,
                    3 => {
                        let owner = NominalTypeId::new(module, 0);
                        Intrinsic::StringFromUtf8 {
                            decoded: ConstructorId::new(owner, 0),
                            invalid: ConstructorId::new(owner, 1),
                        }
                    }
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }
            NodeTag::AddressIntrinsic { module, operation } => {
                let module = *get(&self.modules, module)?;
                if !module.is_builtin_foreign() {
                    return Err(ImageFailure::InvalidRecord);
                }
                use crate::core::packed::Intrinsic;
                let operation = match operation {
                    0 => Intrinsic::AddressNull,
                    1 => Intrinsic::AddressIsNull,
                    2 => Intrinsic::AddressEqual,
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }
            NodeTag::BytesIntrinsic { module, operation } => {
                let module = *get(&self.modules, module)?;
                if !module.is_builtin_bytes() {
                    return Err(ImageFailure::InvalidRecord);
                }
                use crate::core::packed::Intrinsic;
                let operation = match operation {
                    0 => Intrinsic::BytesEmpty,
                    1 => {
                        let owner = NominalTypeId::new(module, 0);
                        Intrinsic::BytesAppendByte {
                            appended: ConstructorId::new(owner, 0),
                            invalid: ConstructorId::new(owner, 1),
                        }
                    }
                    2 => Intrinsic::BytesLength,
                    3 => Intrinsic::BytesEqual,
                    4 => {
                        let owner = NominalTypeId::new(module, 1);
                        Intrinsic::BytesAt {
                            found: ConstructorId::new(owner, 0),
                            invalid: ConstructorId::new(owner, 1),
                        }
                    }
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }

            NodeTag::IntegerMagnitude { negative, bytes } => {
                let bytes = bytes.get(self.fact_table(&self.image.bytes, |p| p.bytes)?)?;
                charge(self.work, bytes.len())?;
                if bytes.last().is_none_or(|b| *b == 0) {
                    return Err(ImageFailure::InvalidRecord);
                }
                let value = Integer::from_sign_magnitude(negative, bytes);
                if value.to_i64().is_some() || value.to_u64().is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.integer(value, ty.into_inner(), origin.take())
                })
            }
            NodeTag::Integer(value) => builder.with_caller_type_work(self.work, |builder| {
                builder.integer(Integer::from_i64(value), ty.into_inner(), origin.take())
            }),
            NodeTag::UnsignedInteger(value) => {
                if value <= i64::MAX as u64 {
                    return Err(ImageFailure::InvalidRecord);
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.integer(Integer::from_u64(value), ty.into_inner(), origin.take())
                })
            }
            NodeTag::Bool(value) => builder.with_caller_type_work(self.work, |builder| {
                builder.boolean(value, ty.into_inner(), origin.take())
            }),
            NodeTag::Unit => builder.with_caller_type_work(self.work, |builder| {
                builder.unit(ty.into_inner(), origin.take())
            }),
            NodeTag::String(range) => {
                let bytes = range.get(self.fact_table(&self.image.bytes, |p| p.bytes)?)?;
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
#[path = "image_provenance_tests.rs"]
mod provenance_tests;

#[cfg(test)]
mod tests {

    #[test]
    fn integer_region_image_preserves_inline_width_digit_storage_and_arithmetic() {
        assert_region_image(
            "import @builtin.regions as Region\nmain : Unit -> Int\nmain () = {\nlet wide = 18446744073709551616\nlet answer = wide * wide\nmatch answer == 340282366920938463463374607431768211456 {\ntrue => 42\nfalse => 0\n}\n}\n",
        );
    }

    #[test]
    fn default_region_entry_image_restores_without_original_sources() {
        assert_region_image(concat!(
            "import @builtin.regions as Region\n",
            "main : Unit -> Int\nmain () = region<R> r {\nusing r {\nmatch (20, 22) {\n(a, b) => match (a + b) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n}\n",
        ));
    }

    #[test]
    fn nominal_region_image_preserves_constructor_identity_and_recursive_aliases() {
        assert_region_image(concat!(
            "import @builtin.regions as Region\n",
            "type Stream = Next(Int, Stream)\nmain : Unit -> Int\nmain () = region<R> r {\n",
            "let rec ones : Stream = Next(21, ones)\nmatch ones {\n",
            "Next(first, rest) => match rest {\nNext(second, ignored) => match (first + second) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n}\n",
        ));
    }

    #[test]
    fn byte_storage_image_restores_literal_and_utf8_result_without_sources() {
        assert_region_image(concat!(
            "import @builtin.regions as Region\nimport @builtin.string as Text\nimport @builtin.bytes as B\n",
            "main : Unit -> Int\nmain () = region<R> r {\n",
            "match Text.from_utf8 (Text.to_utf8 \"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\") {\n",
            "Text.Decoded(text) => Text.byte_length text\nText.InvalidUtf8 => 0\n}\n}\n"
        ));
    }

    fn assert_region_image(source: &str) {
        let tree = SourceTree::new();
        tree.write("entry.ash", source);
        let compiled = compile_path(tree.configuration()).unwrap();
        assert!(compiled.pure_build_input().is_none());
        let (program, provenance) = compiled
            .effect_build_input()
            .expect("generated root/default uses explicit Effect Core");
        let build = encode_effect_for_build(
            program,
            provenance,
            super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        for role in [
            ModuleRoleRecord::BuiltinRegion,
            ModuleRoleRecord::BuiltinRegionFacade,
        ] {
            assert!(build.image.sources.iter().any(|source| source.role == role));
        }
        let bytes = build
            .image
            .encode_bytes(&mut TypeWorkBudget::default())
            .unwrap();
        let expected = build
            .image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        drop(build);
        drop(compiled);
        drop(tree);
        let mut work = TypeWorkBudget::default();
        let decoded = PureImage::decode_bytes(&bytes, &mut work).unwrap();
        decoded
            .admit_expected_native_facts(&expected, &mut work)
            .unwrap();
        let restored = decoded.restore_effect(&mut work).unwrap();
        assert_eq!(
            crate::eval::evaluate_effect(&restored.program)
                .unwrap()
                .value
                .to_string(),
            "42"
        );
    }
    use super::*;

    #[test]
    fn generic_cell_private_image_reconstructs_dependency_proof_and_executes() {
        let (donor, sources) = crate::core::validate::generic_cell_validated_fixture_for_test();
        let provenance = donor
            .registry()
            .type_variables()
            .map(|parameter| {
                let module = parameter.id.module().unwrap();
                let source = sources
                    .iter()
                    .find(|source| source.id() == parameter.origin.primary_span().source())
                    .unwrap();
                (module, std::sync::Arc::new(source.clone()))
            })
            .collect::<std::collections::BTreeMap<_, _>>()
            .into_iter()
            .collect::<Vec<_>>();
        let build = encode_effect_for_build(
            &donor,
            &provenance,
            super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(
            build
                .image
                .sources
                .iter()
                .any(|source| matches!(source.role, ModuleRoleRecord::BuiltinGenericCell))
        );
        let bytes = build
            .image
            .encode_bytes(&mut TypeWorkBudget::default())
            .unwrap();
        let expected = build
            .image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        drop(build);
        drop(donor);
        drop(sources);
        let mut work = TypeWorkBudget::default();
        let decoded = PureImage::decode_bytes(&bytes, &mut work).unwrap();
        decoded
            .admit_expected_native_facts(&expected, &mut work)
            .unwrap();
        let restored = decoded.restore_effect(&mut work).unwrap();
        assert_eq!(
            crate::eval::evaluate_effect(&restored.program)
                .unwrap()
                .value
                .to_string(),
            "42"
        );
    }

    #[test]
    fn generic_cell_image_rejects_missing_duplicate_donor_and_unsealed_scope_facts() {
        let (program, sources, relation) =
            crate::core::validate::generic_cell_source_fixture_for_test(
                include_str!("../../tests/fixtures/generic-cell/retention-entry.ash"),
                Some(include_str!(
                    "../../tests/fixtures/generic-cell/dependency-helper.ash"
                )),
            );
        let provenance = relation
            .iter()
            .map(|(module, id)| {
                (
                    *module,
                    Arc::new(
                        sources
                            .iter()
                            .find(|source| source.id() == *id)
                            .unwrap()
                            .clone(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let build = encode_effect_for_build(
            &program,
            &provenance,
            super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        let original = build
            .image
            .encode_bytes(&mut TypeWorkBudget::default())
            .unwrap();
        let expected = build
            .image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        for case in [
            "missing",
            "duplicate",
            "declaration",
            "donor",
            "kind",
            "prefix",
        ] {
            let mut image =
                PureImage::decode_bytes(&original, &mut TypeWorkBudget::default()).unwrap();
            let slot = *image
                .scope_parameters
                .first()
                .expect("Cell scope has a canonical identity");
            match case {
                "missing" => {
                    image.scope_parameters.remove(0);
                }
                "duplicate" => image.scope_parameters.push(slot),
                "declaration" => {
                    image.scope_parameters[0] = (0..image.native_fact_prefixes.unwrap().parameters)
                        .find(|slot| !image.scope_parameters.contains(slot))
                        .expect("Cell declaration parameters are separate from scopes");
                }
                "donor" => {
                    let TypeVariableIdentity::Resolved { module, .. } =
                        image.parameters[slot as usize].id
                    else {
                        panic!("source scope identity must be resolved")
                    };
                    image.parameters[slot as usize].id = TypeVariableIdentity::Resolved {
                        module,
                        local: u32::MAX,
                    };
                }
                "kind" => {
                    let kind = image.parameters[slot as usize].kind;
                    assert_eq!(image.kinds[kind as usize], KindRecord::Type);
                    image.kinds[kind as usize] = KindRecord::EffectRow;
                }
                "prefix" => {
                    let parameter = image.parameters[slot as usize];
                    let outside = image.native_fact_prefixes.unwrap().parameters;
                    image.parameters.push(parameter);
                    image.scope_parameters[0] = outside;
                }
                _ => unreachable!(),
            }
            let encoded = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
            let image = PureImage::decode_bytes(&encoded, &mut TypeWorkBudget::default()).unwrap();
            assert!(
                image
                    .admit_expected_native_facts(&expected, &mut TypeWorkBudget::default())
                    .is_err(),
                "startup must refuse changed expected facts: {case}"
            );
            // A caller without expected bytes must still face the complete
            // canonical inventory and independent source/Core validation.
            let image = PureImage::decode_bytes(&encoded, &mut TypeWorkBudget::default()).unwrap();
            assert!(
                image
                    .restore_effect(&mut TypeWorkBudget::default())
                    .is_err(),
                "restoration must independently reject malformed scope facts: {case}"
            );
        }
    }

    #[test]
    fn generic_cell_imported_flow_images_rebuild_with_exact_short_and_retry_work() {
        let mut default_refusal_checked = false;
        let mut case = 0;
        for (source, helper, value) in [
            (
                include_str!("../../tests/fixtures/generic-cell/snapshot-entry.ash"),
                include_str!("../../tests/fixtures/generic-cell/dependency-helper.ash"),
                "7",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/recursive-entry.ash"),
                include_str!("../../tests/fixtures/generic-cell/recursive-helper.ash"),
                "9",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/handler-snapshot-entry.ash"),
                include_str!("../../tests/fixtures/generic-cell/dependency-helper.ash"),
                "7",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/tick-entry.ash"),
                "",
                "99",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/reply-mutation-entry.ash"),
                "",
                "(7, 42)",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/intercept-entry.ash"),
                include_str!("../../tests/fixtures/generic-cell/intercept-helper.ash"),
                "7",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/handler-read-entry.ash"),
                "",
                "99",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/handler-write-entry.ash"),
                "",
                "41",
            ),
            (
                include_str!("../../tests/fixtures/generic-cell/handler-forward-entry.ash"),
                "",
                "42",
            ),
        ] {
            case += 1;
            let (program, sources, relation) =
                crate::core::validate::generic_cell_source_fixture_for_test(source, Some(helper));
            let program = if source.contains("90 + 9") {
                let refs = sources.iter().collect::<Vec<_>>();
                let folded =
                    crate::core::transform::fold_effect_literal_primitives(&program).unwrap();
                crate::core::validate_effect_modules(folded, &refs, &relation).unwrap()
            } else {
                program
            };
            let provenance = relation
                .iter()
                .map(|(module, id)| {
                    (
                        *module,
                        Arc::new(
                            sources
                                .iter()
                                .find(|source| source.id() == *id)
                                .unwrap()
                                .clone(),
                        ),
                    )
                })
                .collect::<Vec<_>>();
            let build = encode_effect_for_build(
                &program,
                &provenance,
                super::super::NATIVE_TARGET,
                &mut TypeWorkBudget::default(),
            )
            .unwrap();
            let bytes = build
                .image
                .encode_bytes(&mut TypeWorkBudget::default())
                .unwrap();
            let expected = build
                .image
                .encode_native_expectations(&mut TypeWorkBudget::default())
                .unwrap();
            drop(build);
            drop(program);
            drop(provenance);
            drop(sources);
            let restore = |work: &mut TypeWorkBudget| {
                let image = PureImage::decode_bytes(&bytes, work)?;
                image.admit_expected_native_facts(&expected, work)?;
                image.restore_effect(work)
            };
            let mut standalone = TypeWorkBudget::default();
            let standalone_outcome = match restore(&mut standalone) {
                Ok(restored) => {
                    drop(restored);
                    "complete"
                }
                Err(ImageFailure::Resource) => {
                    default_refusal_checked = true;
                    "resource-refusal"
                }
                Err(ImageFailure::Validation(error))
                    if error.reason() == crate::core::ValidationReason::Resource =>
                {
                    default_refusal_checked = true;
                    "validation-resource-refusal"
                }
                Err(error) => panic!("standalone image refusal must be capacity: {error:?}"),
            };
            eprintln!(
                "imported-flow startup case={case} standalone={standalone_outcome} used={}/{}",
                standalone.used(),
                standalone.limit()
            );
            // Use the same startup owner as the generated runner, carrying
            // framing, expected facts and reconstruction in one cumulative meter.
            if case == 2 {
                assert_eq!(standalone_outcome, "validation-resource-refusal");
            }
            let mut measured = super::super::gas::startup(bytes.len(), expected.len()).unwrap();
            let restored = restore(&mut measured).unwrap_or_else(|error| {
                panic!(
                    "startup image case={case} bytes={} facts={} used={}/{} error={error:?}",
                    bytes.len(),
                    expected.len(),
                    measured.used(),
                    measured.limit()
                )
            });
            eprintln!(
                "imported-flow startup case={case} bytes={} facts={} used={}/{} result={value}",
                bytes.len(),
                expected.len(),
                measured.used(),
                measured.limit()
            );
            assert_eq!(
                crate::eval::evaluate_effect(&restored.program)
                    .unwrap()
                    .value
                    .to_string(),
                value
            );
            drop(restored);
            let mut short = TypeWorkBudget::with_limit(measured.used() - 1);
            assert!(restore(&mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(measured.used());
                drop(restore(&mut exact).unwrap());
                assert_eq!(exact.used(), measured.used());
            }
        }
        assert!(
            default_refusal_checked,
            "the unchanged standalone allowance refuses at least one retained flow"
        );
    }

    #[test]
    fn generic_cell_image_reconstructs_hidden_capture_instead_of_trusting_prior_proof() {
        let (program, sources, relation) =
            crate::core::validate::generic_cell_source_fixture_for_test(
                include_str!("../../tests/fixtures/generic-cell/retention-entry.ash"),
                Some(include_str!(
                    "../../tests/fixtures/generic-cell/dependency-helper.ash"
                )),
            );
        let provenance = relation
            .iter()
            .map(|(module, id)| {
                (
                    *module,
                    Arc::new(
                        sources
                            .iter()
                            .find(|source| source.id() == *id)
                            .unwrap()
                            .clone(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        let build = encode_effect_for_build(
            &program,
            &provenance,
            super::super::NATIVE_TARGET,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        let expected = build
            .image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        let mut image = build.image;
        let handles = image
            .nodes
            .iter()
            .filter_map(|node| match node.tag {
                NodeTag::CellScope {
                    handle,
                    initializer,
                    ..
                } => Some((
                    handle,
                    matches!(image.nodes[initializer as usize].tag, NodeTag::Integer(41)),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(handles.len(), 2);
        let scalar = image.binders[handles.iter().find(|(_, scalar)| *scalar).unwrap().0 as usize];
        let function =
            image.binders[handles.iter().find(|(_, scalar)| !*scalar).unwrap().0 as usize];
        let same_binder = |left, right| match (left, right) {
            (
                BinderIdentity::Resolved {
                    module: a,
                    local: b,
                },
                BinderIdentity::Resolved {
                    module: c,
                    local: d,
                },
            ) => a == c && b == d,
            (BinderIdentity::Generated(a), BinderIdentity::Generated(b)) => a == b,
            _ => false,
        };
        let changed = image
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                matches!(node.tag, NodeTag::Variable(id) if same_binder(id,scalar.id))
                    .then_some(index)
            })
            .collect::<Vec<_>>();
        assert_eq!(changed.len(), 1);
        let changed = changed[0];
        image.nodes[changed].tag = NodeTag::Variable(function.id);
        image.nodes[changed].ty = function.ty;
        let mut binders = 0;
        for node in &image.nodes {
            if let NodeTag::Bind {
                binder,
                initializer,
                ..
            } = node.tag
                && initializer as usize == changed
            {
                image.binders[binder as usize].ty = function.ty;
                binders += 1;
            }
        }
        assert_eq!(binders, 1);
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        let decoded = PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        decoded
            .admit_expected_native_facts(&expected, &mut TypeWorkBudget::default())
            .unwrap();
        let error = match decoded.restore_effect(&mut TypeWorkBudget::default()) {
            Err(error) => error,
            Ok(_) => panic!("changed hidden retention must fail independent image validation"),
        };
        assert!(
            matches!(error, ImageFailure::Validation(ref error)
            if error.reason() == crate::core::ValidationReason::ResourceEscape),
            "{error:?}"
        );
    }

    #[test]
    fn prospective_preparation_source_and_node_sizing_is_paid_and_carried() {
        fn total(source_bytes: usize, nodes: usize, coefficient: usize) -> Result<usize, ()> {
            source_bytes
                .checked_add(nodes)
                .and_then(|p| p.checked_mul(coefficient))
                .ok_or(())
        }
        fn size(
            sources: &[SourceFile],
            nodes: usize,
            work: &mut TypeWorkBudget,
        ) -> Result<(usize, usize), ()> {
            work.charge(1)?;
            let mut bytes = 0usize;
            for source in sources {
                work.charge(1)?;
                bytes = bytes.checked_add(source.text().len()).ok_or(())?;
            }
            Ok((bytes, bytes.checked_add(nodes).ok_or(())?))
        }
        assert!(total(usize::MAX, 1, 1).is_err());
        assert!(total(1, 1, usize::MAX).is_err());
        let sources =
            [SourceFile::new("sizing.ash", "main : Unit -> Int\nmain () = 42\n").unwrap()];
        let mut measured = TypeWorkBudget::with_limit(sources.len() + 1);
        let (bytes, proxy) = size(&sources, 5, &mut measured).unwrap();
        assert_eq!(proxy, bytes + 5);
        let cost = measured.used();
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(size(&sources, 5, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(size(&sources, 5, &mut exact).unwrap(), (bytes, proxy));
                let used = exact.used();
                exact.finish_sizing(total(bytes, 5, 32).unwrap()).unwrap();
                assert_eq!(
                    exact.used(),
                    used,
                    "sizing is inside total, not erased or added as extra fuel"
                );
                exact.charge(exact.remaining()).unwrap();
                assert!(exact.charge(1).is_err());
            }
        }
        let mut empty = TypeWorkBudget::with_limit(1);
        size(&[], 0, &mut empty).unwrap();
        assert!(empty.finish_sizing(total(0, 0, 32).unwrap()).is_err());
    }

    #[test]
    fn native_gas_preparation_refuses_repeated_type_amplification() {
        let source = Arc::new(
            SourceFile::new("amplification.ash", "main : Unit -> Int\nmain () = 42\n").unwrap(),
        );
        let sources = [(ModuleId::new(0), source)];
        let mut work = super::super::gas::preparation(&sources, 1).unwrap();
        let total = work.limit();
        work.charge(150).unwrap();
        let prefix = work.used();
        // Many identical resident children would intern into only two flat
        // records. The complete encoder traversal is still paid; interning
        // never awards expansion credit or bypasses the input-derived meter.
        let ty = IterativeTypeOwner::new(Type::Tuple(vec![Type::Unit; 16_384].into_boxed_slice()));
        let mut encoder = Encoder {
            image: PureImage {
                effect_dialect: true,
                ..PureImage::default()
            },
            structural: HashMap::new(),
            kind_records: HashMap::new(),
            quantifier_vectors: HashMap::new(),
            modules: HashMap::new(),
            sources: HashMap::new(),
            binders: HashMap::new(),
            remapped: Vec::new(),
            prepared_libraries: HashMap::new(),
            native_symbols: HashMap::new(),

            origin_records: HashMap::new(),
            origin_spans: HashMap::new(),
            original_native_symbols: Vec::new(),
            work: &mut work,
        };
        assert!(matches!(
            encoder.encode_structural(StructuralInput::Type(&ty)),
            Err(ImageFailure::Resource)
        ));
        assert!(encoder.work.used() >= prefix && encoder.work.used() <= total);
        assert_eq!(encoder.work.limit(), total);
        println!(
            "native preparation gas amplification: input_nodes=1, repeated_children=16384, allowance={total}, carried_prefix={prefix}, refusal_used={}",
            encoder.work.used()
        );
    }

    #[test]
    fn native_gas_pilot_keeps_framing_overflow_and_amplification_metered() {
        // Proposal-only arithmetic, not a production allowance or new entry.
        let forecast = |image: usize, facts: usize, host: usize| {
            let bytes = image.checked_add(facts).ok_or(ImageFailure::Resource)?;
            let preparation = bytes
                .checked_mul(4)
                .and_then(|n| host.checked_mul(3).and_then(|h| n.checked_add(h)))
                .ok_or(ImageFailure::Resource)?;
            let startup = super::super::gas::startup(image, facts)
                .map_err(|()| ImageFailure::Resource)?
                .limit();
            Ok::<_, ImageFailure>((preparation, startup))
        };
        assert!(forecast(usize::MAX, 1, 0).is_err());
        assert!(forecast(usize::MAX / 4 + 1, 0, 0).is_err());
        assert!(forecast(1, 1, usize::MAX).is_err());
        assert_eq!(forecast(0, 0, 0).unwrap(), (0, 0));

        let tree = SourceTree::new();
        tree.write("entry.ash", "main : Unit -> Int\nmain () = 42\n");
        let compiled = compile_path(tree.configuration()).unwrap();
        let (program, provenance) = compiled.pure_build_input().unwrap();
        let image = encode(program, provenance, &mut TypeWorkBudget::default()).unwrap();
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        let facts = image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        let census = |bytes: &[u8], facts: &[u8], work: &mut TypeWorkBudget| {
            let framed = PureImage::decode_bytes(bytes, work)?;
            framed.compare_native_expectations(facts, work)?;
            forecast(bytes.len(), facts.len(), 0)
        };
        let (_, gas) = forecast(bytes.len(), facts.len(), 0).unwrap();
        let mut measured = TypeWorkBudget::with_limit(gas);
        census(&bytes, &facts, &mut measured).unwrap();
        let required = measured.used();
        assert!(required > 0 && required < gas);
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(census(&bytes, &facts, &mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                census(&bytes, &facts, &mut exact).unwrap();
                assert_eq!(
                    exact.used(),
                    prefix + required,
                    "census never resets or self-awards more gas"
                );
            }
        }
        let mut padded = bytes.clone();
        padded.push(0);
        let mut padded_facts = facts.clone();
        padded_facts.push(0);
        for (input, expected) in [
            (&padded[..], &facts[..]),
            (&bytes[..bytes.len() - 1], &facts[..]),
            (&bytes[..], &padded_facts[..]),
        ] {
            assert!(
                census(input, expected, &mut TypeWorkBudget::with_limit(gas)).is_err(),
                "invalid framing cannot publish semantic gas"
            );
        }

        // 65 physical records describe 2^65-1 logical cells. The forecast
        // depends on actual framed bytes, never this exponential expansion.
        let mut compact = PureImage {
            effect_dialect: true,
            ..PureImage::default()
        };
        compact.types.push(TypeRecord {
            tag: TypeTag::Unit,
            children: Slice { start: 0, len: 0 },
        });
        for slot in 1..=64 {
            let start = compact.type_children.len();
            compact
                .type_children
                .extend_from_slice(&[slot - 1, slot - 1]);
            compact.types.push(TypeRecord {
                tag: TypeTag::Tuple,
                children: Slice::of(&compact.type_children, start).unwrap(),
            });
        }
        compact.native_fact_prefixes = Some(NativeFactPrefixes::seal(&compact).unwrap());
        let encoded = compact
            .encode_bytes(&mut TypeWorkBudget::default())
            .unwrap();
        let expected = compact
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        let (_, compact_gas) = forecast(encoded.len(), expected.len(), 0).unwrap();
        assert!(
            compact_gas < 100_000,
            "a small physical carrier grants only linear byte gas"
        );
        let mut limited = TypeWorkBudget::with_limit(compact_gas);
        let compact = PureImage::decode_bytes(&encoded, &mut limited).unwrap();
        compact
            .compare_native_expectations(&expected, &mut limited)
            .unwrap();
        let mut decoder = Decoder {
            image: &compact,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Borrowed(&[]),
            modules: CoordinateStorage::Borrowed(&[]),
            work: &mut limited,
        };
        assert!(matches!(decoder.ty(64), Err(ImageFailure::Resource)));
        assert!(decoder.work.used() <= compact_gas);
        println!(
            "proposal-only gas safety: framed_census={required}, framed_allowance={gas}, compact_records=65, compact_bytes={}, compact_facts={}, compact_allowance={compact_gas}, refusal_used={}",
            encoded.len(),
            expected.len(),
            decoder.work.used()
        );
    }

    #[test]
    fn private_u32_wire_is_canonical_bounded_and_retryable() {
        for (value, expected) in [
            (0, vec![0]),
            (127, vec![127]),
            (128, vec![128, 1]),
            (16383, vec![255, 127]),
            (16384, vec![128, 128, 1]),
            (u32::MAX, vec![255, 255, 255, 255, 15]),
        ] {
            for prefix in [0, 17] {
                for _ in 0..2 {
                    let mut work = TypeWorkBudget::with_limit(prefix + expected.len());
                    work.charge(prefix).unwrap();
                    let mut writer = WireWriter {
                        output: WireOutput::Encoded(Vec::new()),
                        work: &mut work,
                    };
                    value.write(&mut writer).unwrap();
                    let WireOutput::Encoded(bytes) = writer.output else {
                        unreachable!()
                    };
                    assert_eq!(bytes, expected);
                    assert_eq!(work.used(), prefix + expected.len());
                    let mut read_work = TypeWorkBudget::with_limit(prefix + bytes.len());
                    read_work.charge(prefix).unwrap();
                    let mut reader = WireReader {
                        bytes: &bytes,
                        offset: 0,
                        work: &mut read_work,
                    };
                    assert_eq!(u32::read(&mut reader).unwrap(), value);
                    assert_eq!(reader.offset, bytes.len());
                    assert_eq!(read_work.used(), prefix + bytes.len());
                }
                let mut short = TypeWorkBudget::with_limit(prefix + expected.len() - 1);
                short.charge(prefix).unwrap();
                assert!(
                    u32::read(&mut WireReader {
                        bytes: &expected,
                        offset: 0,
                        work: &mut short
                    })
                    .is_err()
                );
                let mut short = TypeWorkBudget::with_limit(prefix + expected.len() - 1);
                short.charge(prefix).unwrap();
                let mut writer = WireWriter {
                    output: WireOutput::Encoded(Vec::new()),
                    work: &mut short,
                };
                assert!(value.write(&mut writer).is_err());
                assert!(matches!(writer.output, WireOutput::Encoded(bytes) if bytes.is_empty()));
            }
        }
        for bytes in [
            &[128][..],
            &[128, 0],
            &[129, 0],
            &[255, 255, 255, 255, 16],
            &[128, 128, 128, 128, 128, 0],
        ] {
            assert!(matches!(
                u32::read(&mut WireReader {
                    bytes,
                    offset: 0,
                    work: &mut TypeWorkBudget::default()
                }),
                Err(ImageFailure::InvalidEncoding)
            ));
        }
        assert_eq!(Slice::MINIMUM, 2);
        assert_eq!(NativeFactPrefixes::MINIMUM, 12);
    }
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
        // Independent native facts use the same canonical wire traversal.
        // Comparison pays each byte once, with no throwaway encoded allocation.
        let expected = image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        let comparison_cost = expected.len() + 1;
        let mut comparison = TypeWorkBudget::with_limit(comparison_cost);
        image
            .compare_native_expectations(&expected, &mut comparison)
            .unwrap();
        assert_eq!(comparison.used(), comparison_cost);
        let mut prefixed = TypeWorkBudget::with_limit(comparison_cost + 37);
        prefixed.charge(37).unwrap();
        image
            .compare_native_expectations(&expected, &mut prefixed)
            .unwrap();
        assert_eq!(prefixed.used(), comparison_cost + 37);
        assert!(matches!(
            image.compare_native_expectations(
                &expected,
                &mut TypeWorkBudget::with_limit(comparison_cost - 1)
            ),
            Err(ImageFailure::Resource)
        ));
        let mut trailing_expected = expected.clone();
        trailing_expected.push(0);
        let mut altered_expected = expected.clone();
        *altered_expected.last_mut().unwrap() ^= 1;
        for invalid in [
            &expected[..expected.len() - 1],
            trailing_expected.as_slice(),
            altered_expected.as_slice(),
        ] {
            assert!(matches!(
                image.compare_native_expectations(invalid, &mut TypeWorkBudget::default()),
                Err(ImageFailure::InvalidRecord)
            ));
        }
        let mut malformed_prefix = bytes.clone();
        let prefix_start = PRIVATE_MAGIC.len() + 1;
        let mut prefix_work = TypeWorkBudget::default();
        let mut prefix_reader = WireReader {
            bytes: &bytes[prefix_start..],
            offset: 0,
            work: &mut prefix_work,
        };
        u32::read(&mut prefix_reader).unwrap();
        // Preserve a canonical integer spelling but make its claimed original
        // table extent impossible. This tests the fact-prefix boundary rather
        // than an incidental fixed-width layout.
        malformed_prefix.splice(
            prefix_start..prefix_start + prefix_reader.offset,
            [255, 255, 255, 255, 15],
        );
        assert!(matches!(
            PureImage::decode_bytes(&malformed_prefix, &mut TypeWorkBudget::default()),
            Err(ImageFailure::InvalidRecord),
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
    fn private_structural_wire_preserves_type_depth_and_rejects_mixed_children() {
        const LIMIT: usize = crate::core::CORE_PAYLOAD_DEPTH_LIMIT;
        let source = SourceFile::new("structural-wire.ash", "()").unwrap();
        let module = ModuleId::from(source.id());
        let modules = [module];

        // Only construction shape is under test. Final registry/kind/Core
        // authentication remains mandatory before any image can execute.
        fn record(image: &mut PureImage, tag: TypeTag, children: &[u32]) -> u32 {
            let start = image.type_children.len();
            image.type_children.extend_from_slice(children);
            let slot = index(image.types.len()).unwrap();
            image.types.push(TypeRecord {
                tag,
                children: Slice::of(&image.type_children, start).unwrap(),
            });
            slot
        }
        fn chain(image: &mut PureImage, tag: TypeTag, depth: usize, left_spine: bool) -> u32 {
            let leaf = record(image, TypeTag::Unit, &[]);
            let mut root = leaf;
            for _ in 0..depth {
                let children = if left_spine {
                    [root, leaf]
                } else {
                    [leaf, root]
                };
                root = record(image, tag, &children);
            }
            root
        }
        fn row(image: &mut PureImage, ty: u32) -> u32 {
            let argument = record(image, TypeTag::ArgumentType, &[ty]);
            let instance = record(
                image,
                TypeTag::Instance(EffectIdentity {
                    module: 0,
                    local: 0,
                }),
                &[argument],
            );
            record(
                image,
                TypeTag::Row {
                    known: 1,
                    tail: None,
                },
                &[instance],
            )
        }
        fn decode(
            image: &mut PureImage,
            root: u32,
            modules: &[ModuleId],
        ) -> Result<(), ImageFailure> {
            let mut work = TypeWorkBudget::default();
            charge(&mut work, 13)?;
            image.native_fact_prefixes = Some(NativeFactPrefixes::seal(image)?);
            let bytes = image.encode_bytes(&mut work)?;
            let wire = PureImage::decode_bytes(&bytes, &mut work)?;
            let mut decoder = Decoder {
                image: &wire,
                source_declaration_catalogs: HashMap::new(),

                decoded_types: HashMap::new(),
                decoded_rows: HashMap::new(),
                expected_fact_prefixes: None,
                sources: CoordinateStorage::Borrowed(&[]),
                modules: CoordinateStorage::Borrowed(modules),
                work: &mut work,
            };
            // Dropping either successful Types/Rows or partially accumulated
            // heterogeneous results must retain the production iterative owners.
            let result = decoder.structural(root).map(drop);
            assert!(
                work.remaining() > work.limit() / 2,
                "depth refusal is not work exhaustion"
            );
            result
        }
        let image = || PureImage {
            effect_dialect: true,
            ..PureImage::default()
        };

        for depth in [LIMIT, LIMIT + 1] {
            let mut carrier = image();
            let ty = chain(&mut carrier, TypeTag::Function, depth, false);
            let root = row(&mut carrier, ty);
            let result = decode(&mut carrier, root, &modules);
            if depth == LIMIT {
                assert!(result.is_ok(), "row wrappers add no Type depth: {result:?}");
            } else {
                assert!(matches!(result, Err(ImageFailure::Resource)));
            }
        }
        for depth in [LIMIT - 1, LIMIT] {
            let mut carrier = image();
            let ty = chain(&mut carrier, TypeTag::Function, depth, false);
            let effects = row(&mut carrier, ty);
            let unit = record(&mut carrier, TypeTag::Unit, &[]);
            let root = record(
                &mut carrier,
                TypeTag::EffectfulFunction,
                &[unit, unit, effects],
            );
            let result = decode(&mut carrier, root, &modules);
            if depth == LIMIT - 1 {
                assert!(result.is_ok(), "row Types inherit outer depth: {result:?}");
            } else {
                assert!(matches!(result, Err(ImageFailure::Resource)));
            }
        }
        let mut carrier = image();
        let root = chain(&mut carrier, TypeTag::Application, LIMIT + 17, true);
        assert!(decode(&mut carrier, root, &modules).is_ok());
        let root = chain(&mut carrier, TypeTag::Application, LIMIT + 1, false);
        assert!(matches!(
            decode(&mut carrier, root, &modules),
            Err(ImageFailure::Resource)
        ));

        let mut carrier = image();
        let deep = chain(&mut carrier, TypeTag::Function, LIMIT, false);
        let valid_argument = record(&mut carrier, TypeTag::ArgumentType, &[deep]);
        let unit = record(&mut carrier, TypeTag::Unit, &[]);
        let mixed = record(
            &mut carrier,
            TypeTag::Instance(EffectIdentity {
                module: 0,
                local: 0,
            }),
            &[valid_argument, unit],
        );
        assert!(matches!(
            decode(&mut carrier, mixed, &modules),
            Err(ImageFailure::InvalidRecord)
        ));
        let forward = index(carrier.types.len()).unwrap();
        let root = record(&mut carrier, TypeTag::Function, &[unit, forward]);
        assert!(matches!(
            decode(&mut carrier, root, &modules),
            Err(ImageFailure::InvalidRecord)
        ));
        let bad_row = record(
            &mut carrier,
            TypeTag::Row {
                known: 2,
                tail: None,
            },
            &[mixed],
        );
        assert!(matches!(
            decode(&mut carrier, bad_row, &modules),
            Err(ImageFailure::InvalidRecord)
        ));

        // The trusted encoder must use the same boundary as the independently
        // decoded private wire; no extra Core program or host build is needed.
        fn function_type(depth: usize) -> IterativeTypeOwner {
            let mut ty = Type::Unit;
            for _ in 0..depth {
                ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
            }
            IterativeTypeOwner::new(ty)
        }
        fn encode(input: StructuralInput<'_>, module: ModuleId) -> Result<(), ImageFailure> {
            let mut work = TypeWorkBudget::default();
            let mut encoder = Encoder {
                image: PureImage {
                    effect_dialect: true,
                    ..PureImage::default()
                },
                structural: HashMap::new(),
                kind_records: HashMap::new(),
                quantifier_vectors: HashMap::new(),
                modules: HashMap::from([(module, 0)]),
                sources: HashMap::new(),
                binders: HashMap::new(),
                remapped: Vec::new(),
                prepared_libraries: HashMap::new(),
                native_symbols: HashMap::new(),

                origin_records: HashMap::new(),
                origin_spans: HashMap::new(),
                original_native_symbols: Vec::new(),
                work: &mut work,
            };
            let result = encoder.encode_structural(input).map(|_| ());
            assert!(
                work.remaining() > work.limit() / 2,
                "depth refusal is not work exhaustion"
            );
            result
        }
        let effect = crate::types::EffectId::new(module, 0);
        for depth in [LIMIT - 1, LIMIT, LIMIT + 1] {
            let ty = function_type(depth);
            let effects = crate::types::EffectRow::closed(Box::new([
                crate::types::EffectInstance::new_kinded(
                    effect,
                    Box::new([crate::types::KindedArgument::TypeArg(ty.into_inner())]),
                ),
            ]));
            let result = encode(StructuralInput::Row(&effects), module);
            if depth <= LIMIT {
                assert!(
                    result.is_ok(),
                    "encoder row wrappers add no depth: {result:?}"
                );
            } else {
                assert!(matches!(result, Err(ImageFailure::Resource)));
            }
            let root = IterativeTypeOwner::new(Type::EffectfulFunction(
                Box::new(Type::Unit),
                Box::new(crate::types::ComputationType::new(Type::Unit, effects)),
            ));
            let result = encode(StructuralInput::Type(&root), module);
            if depth < LIMIT {
                assert!(
                    result.is_ok(),
                    "encoder row Types inherit outer depth: {result:?}"
                );
            } else {
                assert!(matches!(result, Err(ImageFailure::Resource)));
            }
        }
    }

    #[test]
    fn ordinary_bytes_lookup_image_keeps_canonical_roles_and_paid_refusal() {
        let tree = SourceTree::new();
        tree.write(
            "entry.ash",
            r#"import @builtin.bytes as B
main : Unit -> (Int, Bool, Int, Bool, Bool)
main () = {
    let bytes = match B.append_byte (B.empty (), 255) {
        B.BytesAppended(value) => value
        B.InvalidByte => B.empty ()
    }
    let byte = match B.at (bytes, 0) {
        B.ByteAt(value) => value
        B.InvalidIndex => 0
    }
    let outside = match B.at (bytes, 1) {
        B.ByteAt(_) => false
        B.InvalidIndex => true
    }
    let empty = match B.at (B.empty (), 0) {
        B.ByteAt(_) => false
        B.InvalidIndex => true
    }
    (byte, B.equal (bytes, bytes), B.length bytes, outside, empty)
}
"#,
        );
        let compiled = compile_path(tree.configuration()).unwrap();
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let mut work = TypeWorkBudget::default();
        let image =
            encode_effect_for_build(program, provenance, super::super::NATIVE_TARGET, &mut work)
                .unwrap()
                .image;
        let required = work.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                encode_effect_for_build(
                    program,
                    provenance,
                    super::super::NATIVE_TARGET,
                    &mut short
                ),
                Err(NativeImageFailure::Image(ImageFailure::Resource))
            ));
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            encode_effect_for_build(program, provenance, super::super::NATIVE_TARGET, &mut exact)
                .unwrap();
            assert_eq!(exact.used(), prefix + required);
        }
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        let expected = image
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap();
        drop(compiled);
        drop(tree);
        let restore = |bytes: &[u8], work: &mut TypeWorkBudget| {
            let image = PureImage::decode_bytes(bytes, work)?;
            image.admit_expected_native_facts(&expected, work)?;
            image.restore_effect(work)
        };
        let mut measured = TypeWorkBudget::default();
        let restored = restore(&bytes, &mut measured).unwrap();
        assert_eq!(
            crate::eval::evaluate_effect(&restored.program)
                .unwrap()
                .value
                .to_string(),
            "(255, true, 1, true, true)"
        );
        let required = measured.used();
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(
                restore(&bytes, &mut short).is_err(),
                "one-short work can refuse during final Core validation as well as decoding"
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                restore(&bytes, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + required);
            }
        }
        let canonical = || PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        for change in 0..5 {
            let mut changed = canonical();
            let builtin = changed
                .sources
                .iter()
                .position(|s| matches!(s.role, ModuleRoleRecord::BuiltinBytes))
                .unwrap();
            match change {
                0 => changed.sources[builtin].role = ModuleRoleRecord::Ordinary,
                1 => {
                    let range = changed.sources[builtin].text;
                    changed.bytes[usize::try_from(range.start).unwrap()] = b'X';
                }
                2 => {
                    let record = changed.sources[builtin];
                    changed.sources.push(record);
                }
                3 | 4 => {
                    let ordinary = index(
                        changed
                            .sources
                            .iter()
                            .position(|s| matches!(s.role, ModuleRoleRecord::Ordinary))
                            .unwrap(),
                    )
                    .unwrap();
                    let node = changed
                        .nodes
                        .iter_mut()
                        .find(|node| {
                            matches!(
                                node.tag,
                                NodeTag::RegionBuffer {
                                    source: 1,
                                    operation: 4,
                                    ..
                                }
                            )
                        })
                        .unwrap();
                    let NodeTag::RegionBuffer {
                        module, operation, ..
                    } = &mut node.tag
                    else {
                        unreachable!()
                    };
                    if change == 3 {
                        *module = Some(ordinary);
                    } else {
                        *operation = 255;
                    }
                }
                _ => unreachable!(),
            }
            assert!(
                changed
                    .restore_effect(&mut TypeWorkBudget::default())
                    .is_err(),
                "forged Bytes authority {change}"
            );
        }
    }

    #[test]
    fn decoded_type_values_are_local_paid_and_never_cross_fact_prefixes() {
        fn image() -> PureImage {
            PureImage {
                effect_dialect: true,
                types: vec![
                    TypeRecord {
                        tag: TypeTag::Int,
                        children: Slice { start: 0, len: 0 },
                    },
                    TypeRecord {
                        tag: TypeTag::Unit,
                        children: Slice { start: 0, len: 0 },
                    },
                    TypeRecord {
                        tag: TypeTag::Function,
                        children: Slice { start: 0, len: 2 },
                    },
                    TypeRecord {
                        tag: TypeTag::Tuple,
                        children: Slice { start: 2, len: 2 },
                    },
                ],
                type_children: vec![0, 1, 2, 2],
                ..PureImage::default()
            }
        }
        fn decode_repeated(
            image: &PureImage,
            work: &mut TypeWorkBudget,
            prefix: bool,
        ) -> Result<(), ImageFailure> {
            let mut decoder = Decoder {
                image,
                source_declaration_catalogs: HashMap::new(),

                decoded_types: HashMap::new(),
                decoded_rows: HashMap::new(),
                expected_fact_prefixes: prefix.then(|| NativeFactPrefixes::seal(image).unwrap()),
                sources: CoordinateStorage::Borrowed(&[]),
                modules: CoordinateStorage::Borrowed(&[]),
                work,
            };
            let expected = Type::Tuple(Box::new([
                Type::Function(Box::new(Type::Int), Box::new(Type::Unit)),
                Type::Function(Box::new(Type::Int), Box::new(Type::Unit)),
            ]));
            drop(decoder.ty(2)?);
            for _ in 0..8 {
                let value = decoder.ty(3)?;
                assert_eq!(&*value, &expected);
            }
            assert_eq!(decoder.decoded_types.len(), 2 * usize::from(!prefix));
            Ok(())
        }
        let image = image();
        let mut measured = TypeWorkBudget::default();
        decode_repeated(&image, &mut measured, false).unwrap();
        let required = measured.used();
        let mut uncached = TypeWorkBudget::default();
        decode_repeated(&image, &mut uncached, true).unwrap();
        assert!(
            required < uncached.used(),
            "paid representation sharing removes real reconstruction work"
        );
        for prefix in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(matches!(
                decode_repeated(&image, &mut short, false),
                Err(ImageFailure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                decode_repeated(&image, &mut exact, false).unwrap();
                assert_eq!(exact.used(), prefix + required);
            }
        }
        // A full-mode suffix value must not make that coordinate readable as
        // original declaration metadata, even in the same decoder instance.
        let prefixes = NativeFactPrefixes::seal(&image).unwrap();
        let mut suffix = image;
        suffix.types.push(TypeRecord {
            tag: TypeTag::Bool,
            children: Slice { start: 0, len: 0 },
        });
        let mut work = TypeWorkBudget::default();
        let mut decoder = Decoder {
            image: &suffix,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Borrowed(&[]),
            modules: CoordinateStorage::Borrowed(&[]),
            work: &mut work,
        };
        assert_eq!(&*decoder.ty(4).unwrap(), &Type::Bool);
        decoder.expected_fact_prefixes = Some(prefixes);
        assert!(matches!(decoder.ty(4), Err(ImageFailure::InvalidRecord)));
        drop(decoder);
        // A fresh image/context never imports the preceding decoder's values.
        let mut changed = suffix;
        changed.types[0].tag = TypeTag::Bool;
        let mut fresh = Decoder {
            image: &changed,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Borrowed(&[]),
            modules: CoordinateStorage::Borrowed(&[]),
            work: &mut work,
        };
        assert_eq!(&*fresh.ty(0).unwrap(), &Type::Bool);
    }

    #[test]
    fn decoded_type_subtree_reuse_preserves_the_complete_depth_boundary() {
        let limit = crate::core::CORE_PAYLOAD_DEPTH_LIMIT;
        let mut image = PureImage {
            effect_dialect: true,
            ..PureImage::default()
        };
        image.types.push(TypeRecord {
            tag: TypeTag::Unit,
            children: Slice { start: 0, len: 0 },
        });
        for slot in 1..=limit + 1 {
            let start = image.type_children.len();
            image
                .type_children
                .extend_from_slice(&[0, index(slot - 1).unwrap()]);
            image.types.push(TypeRecord {
                tag: TypeTag::Function,
                children: Slice::of(&image.type_children, start).unwrap(),
            });
        }
        let mut work = TypeWorkBudget::default();
        let mut decoder = Decoder {
            image: &image,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Borrowed(&[]),
            modules: CoordinateStorage::Borrowed(&[]),
            work: &mut work,
        };
        drop(decoder.ty(index(limit).unwrap()).unwrap());
        assert_eq!(
            decoder.decoded_types[&(index(limit).unwrap(), 0, 0)].depth,
            limit
        );
        for _ in 0..2 {
            assert!(matches!(
                decoder.ty(index(limit + 1).unwrap()),
                Err(ImageFailure::Resource)
            ));
        }
        assert!(
            decoder.work.remaining() > decoder.work.limit() / 2,
            "refusal is structural depth, not exhausted work"
        );
        assert!(
            !decoder
                .decoded_types
                .contains_key(&(index(limit + 1).unwrap(), 0, 0))
        );
    }

    #[test]
    fn exact_quantified_representation_borrowed_keys_keep_identity_under_collisions() {
        use std::hash::BuildHasherDefault;
        #[derive(Default)]
        struct Colliding;
        impl Hasher for Colliding {
            fn finish(&self) -> u64 {
                0
            }
            fn write(&mut self, _: &[u8]) {}
        }
        #[derive(Default)]
        struct Stream(Vec<u8>);
        impl Hasher for Stream {
            fn finish(&self) -> u64 {
                0
            }
            fn write(&mut self, bytes: &[u8]) {
                self.0.extend_from_slice(bytes);
            }
        }
        let cases = [
            (TypeTag::Tuple, vec![]),
            (TypeTag::Tuple, vec![2]),
            (TypeTag::Tuple, vec![2, 3]),
            (TypeTag::Tuple, vec![3, 2]),
            (TypeTag::Application, vec![2, 3]),
            (TypeTag::ArgumentRow, vec![2]),
            (TypeTag::ArgumentType, vec![2]),
            (
                TypeTag::Forall {
                    parameters: Slice { start: 0, len: 1 },
                },
                vec![2],
            ),
            (
                TypeTag::Forall {
                    parameters: Slice { start: 1, len: 1 },
                },
                vec![2],
            ),
            (
                TypeTag::Forall {
                    parameters: Slice { start: 0, len: 2 },
                },
                vec![2],
            ),
            (
                TypeTag::Row {
                    known: 1,
                    tail: None,
                },
                vec![2, 3],
            ),
            (
                TypeTag::Row {
                    known: 2,
                    tail: None,
                },
                vec![2, 3],
            ),
            (
                TypeTag::Row {
                    known: 1,
                    tail: Some(TypeVariableIdentity::Generated(7)),
                },
                vec![2, 3],
            ),
            (
                TypeTag::Row {
                    known: 1,
                    tail: Some(TypeVariableIdentity::Generated(8)),
                },
                vec![2, 3],
            ),
        ];
        let mut map = HashMap::<StructuralKey, usize, BuildHasherDefault<Colliding>>::default();
        for (slot, (tag, children)) in cases.iter().enumerate() {
            let owned = StructuralKey(*tag, children.clone().into_boxed_slice());
            let probe = StructuralProbe(*tag, children);
            let view: &(dyn StructuralKeyView + '_) = &probe;
            let mut left = Stream::default();
            let mut right = Stream::default();
            owned.hash(&mut left);
            view.hash(&mut right);
            assert_eq!(left.0, right.0, "Borrow must preserve the full hash stream");
            assert!(map.insert(owned, slot).is_none());
        }
        for (slot, (tag, children)) in cases.iter().enumerate() {
            let probe = StructuralProbe(*tag, children);
            let view: &(dyn StructuralKeyView + '_) = &probe;
            assert_eq!(map.get(view), Some(&slot));
            assert_eq!(map.len(), cases.len());
        }
    }

    #[test]
    fn exact_quantified_representation_sharing_preserves_order_kinds_and_paid_prefixes() {
        use crate::types::{Kind, TypeVariableId};
        fn encode(
            work: &mut TypeWorkBudget,
        ) -> Result<(PureImage, u32, u32, NativeFactPrefixes), ImageFailure> {
            let mut encoder = Encoder {
                image: PureImage {
                    effect_dialect: true,
                    ..PureImage::default()
                },
                structural: HashMap::new(),
                kind_records: HashMap::new(),
                quantifier_vectors: HashMap::new(),
                modules: HashMap::new(),
                sources: HashMap::new(),
                binders: HashMap::new(),
                remapped: Vec::new(),
                prepared_libraries: HashMap::new(),
                native_symbols: HashMap::new(),

                origin_records: HashMap::new(),
                origin_spans: HashMap::new(),
                original_native_symbols: Vec::new(),
                work,
            };
            let a = TypeVariableId::generated(9);
            let r = TypeVariableId::generated(10);
            let scheme =
                |parameters: Box<[_]>| Type::Forall(parameters, Box::new(Type::Variable(a)));
            let first =
                encoder.encode_type(&scheme(Box::new([(a, Kind::Type), (r, Kind::EffectRow)])))?;
            let first_counts = (
                encoder.image.types.len(),
                encoder.image.kinds.len(),
                encoder.image.quantifiers.len(),
            );
            for _ in 0..8 {
                let repeated = encoder
                    .encode_type(&scheme(Box::new([(a, Kind::Type), (r, Kind::EffectRow)])))?;
                assert_eq!(
                    first, repeated,
                    "identical original identities and ordered kinds share passive records"
                );
                assert_eq!(
                    first_counts,
                    (
                        encoder.image.types.len(),
                        encoder.image.kinds.len(),
                        encoder.image.quantifiers.len()
                    )
                );
            }
            // A previously interned child does not authorize a deeper input.
            // The complete Visit/depth walk must still refuse before a hit.
            let mut deep = IterativeTypeOwner::new(Type::Unit);
            for _ in 0..=crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                deep = IterativeTypeOwner::new(Type::Function(
                    Box::new(Type::Unit),
                    Box::new(deep.into_inner()),
                ));
            }
            assert!(matches!(
                encoder.encode_type(&deep),
                Err(ImageFailure::Resource)
            ));
            for parameters in [
                Box::new([(r, Kind::EffectRow), (a, Kind::Type)]),
                Box::new([(a, Kind::EffectRow), (r, Kind::Type)]),
                Box::new([
                    (a, Kind::Type),
                    (TypeVariableId::generated(11), Kind::EffectRow),
                ]),
                Box::new([
                    (a, Kind::Type),
                    (r, Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                ]),
            ] {
                assert_ne!(first, encoder.encode_type(&scheme(parameters))?);
            }
            let prefix = NativeFactPrefixes::seal(&encoder.image)?;
            let suffix = encoder.encode_type(&scheme(Box::new([
                (a, Kind::Type),
                (TypeVariableId::generated(12), Kind::EffectRow),
            ])))?;
            Ok((encoder.image, first, suffix, prefix))
        }
        let mut measured = TypeWorkBudget::default();
        let (image, first, suffix, prefix) = encode(&mut measured).unwrap();
        let required = measured.used();
        for used in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(used + required - 1);
            short.charge(used).unwrap();
            assert!(matches!(encode(&mut short), Err(ImageFailure::Resource)));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(used + required);
                exact.charge(used).unwrap();
                encode(&mut exact).unwrap();
                assert_eq!(exact.used(), used + required);
            }
        }
        let mut work = TypeWorkBudget::default();
        let mut decoder = Decoder {
            image: &image,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: Some(prefix),
            sources: CoordinateStorage::Borrowed(&[]),
            modules: CoordinateStorage::Borrowed(&[]),
            work: &mut work,
        };
        assert_eq!(
            &*decoder.ty(first).unwrap(),
            &Type::Forall(
                Box::new([
                    (TypeVariableId::generated(9), Kind::Type),
                    (TypeVariableId::generated(10), Kind::EffectRow)
                ]),
                Box::new(Type::Variable(TypeVariableId::generated(9)))
            )
        );
        assert!(matches!(
            decoder.ty(suffix),
            Err(ImageFailure::InvalidRecord)
        ));
    }

    #[test]
    fn exact_origin_record_sharing_keeps_depth_prefix_and_paid_retry_boundaries() {
        fn encode(
            source: &SourceFile,
            origin: &Origin,
            suffix: Span,
            work: &mut TypeWorkBudget,
        ) -> Result<(PureImage, u32, NativeFactPrefixes, u32), ImageFailure> {
            let mut encoder = Encoder {
                image: PureImage {
                    effect_dialect: true,
                    ..PureImage::default()
                },
                structural: HashMap::new(),
                kind_records: HashMap::new(),
                quantifier_vectors: HashMap::new(),
                modules: HashMap::from([(ModuleId::from(source.id()), 0)]),
                sources: HashMap::from([(source.id(), 0)]),
                binders: HashMap::new(),
                remapped: Vec::new(),
                prepared_libraries: HashMap::new(),
                native_symbols: HashMap::new(),

                origin_records: HashMap::new(),
                origin_spans: HashMap::new(),
                original_native_symbols: Vec::new(),
                work,
            };
            let first = encoder.encode_origin(origin)?;
            let repeated = encoder.encode_origin(origin)?;
            assert_eq!(first, repeated);
            let prefix = NativeFactPrefixes::seal(&encoder.image)?;
            let suffix = encoder.encode_origin(&Origin::Source(suffix))?;
            Ok((encoder.image, first, prefix, suffix))
        }
        let source = SourceFile::new("origin-record-sharing.ash", "A B").unwrap();
        let first = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let second = source.span(ByteRange::new(2, 3).unwrap()).unwrap();
        let origin = Origin::Related {
            primary: Box::new(Origin::Generated {
                cause: Box::new(Origin::Source(first)),
                reason: GeneratedReason::TypeChecking,
            }),
            related: vec![second],
        };
        let mut measured = TypeWorkBudget::default();
        let (image, root, prefix, suffix) =
            encode(&source, &origin, second, &mut measured).unwrap();
        assert_eq!(image.origins.len(), 4);
        assert_eq!(image.spans.len(), 1);
        assert_eq!(
            image
                .origins
                .iter()
                .copied()
                .collect::<std::collections::HashSet<_>>()
                .len(),
            image.origins.len()
        );
        let required = measured.used();
        for used in [0, 7] {
            let mut short = TypeWorkBudget::with_limit(used + required - 1);
            short.charge(used).unwrap();
            assert!(matches!(
                encode(&source, &origin, second, &mut short),
                Err(ImageFailure::Resource)
            ));
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(used + required);
                exact.charge(used).unwrap();
                encode(&source, &origin, second, &mut exact).unwrap();
                assert_eq!(exact.used(), used + required);
            }
        }
        let mut work = TypeWorkBudget::default();
        let modules = [ModuleId::from(source.id())];
        let mut decoder = Decoder {
            image: &image,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Borrowed(std::slice::from_ref(&source)),
            modules: CoordinateStorage::Borrowed(&modules),
            work: &mut work,
        };
        assert_eq!(decoder.origin(root).unwrap().0.as_ref(), Some(&origin));
        decoder.origin(suffix).unwrap();
        decoder.expected_fact_prefixes = Some(prefix);
        assert_eq!(decoder.origin(root).unwrap().0.as_ref(), Some(&origin));
        assert!(matches!(
            decoder.origin(suffix),
            Err(ImageFailure::InvalidRecord)
        ));
        drop(decoder);
        let mut deep = OriginOwner(Some(Origin::Source(first)));
        for _ in 0..crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
            deep = OriginOwner(Some(Origin::Generated {
                cause: Box::new(deep.take()),
                reason: GeneratedReason::TypeChecking,
            }));
        }
        encode(
            &source,
            deep.0.as_ref().unwrap(),
            second,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        deep = OriginOwner(Some(Origin::Generated {
            cause: Box::new(deep.take()),
            reason: GeneratedReason::TypeChecking,
        }));
        assert!(matches!(
            encode(
                &source,
                deep.0.as_ref().unwrap(),
                second,
                &mut TypeWorkBudget::default()
            ),
            Err(ImageFailure::Resource)
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

// These records extend src/build/image.rs's existing flat carrier, WireReader,
// WireWriter, push/append/get helpers and single caller TypeWorkBudget. They are
// insertion fragments, not a second image format or a compiled implementation.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ModuleRoleRecord {
    Ordinary,
    BuiltinRegion,
    BuiltinRegionFacade,
    BuiltinForeign,
    BuiltinCell,
    BuiltinGenericCell,
    BuiltinString,
    BuiltinBytes,
}

// Add role: ModuleRoleRecord to SourceRecord. Never infer it from the path.
// Ordinary restoration stays DirectCoreSource. BuiltinForeign restoration must
// use the owning module helper and compare original bytes against FOREIGN_SOURCE
// with a byte precharge; it cannot grant a role to arbitrary embedded contents.

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct EffectIdentity {
    module: u32,
    local: u32,
}

#[derive(Clone, Copy, Debug)]
struct OperationIdentity {
    owner: EffectIdentity,
    local: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum TypeVariableIdentity {
    Resolved { module: u32, local: u32 },
    Generated(u32),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum KindRecord {
    Type,
    EffectRow,
    Function { domain: u32, codomain: u32 },
}

#[derive(Clone, Copy, Debug)]
struct ParameterRecord {
    id: TypeVariableIdentity,
    spelling: Slice,
    kind: u32,
    origin: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct QuantifierRecord {
    id: TypeVariableIdentity,
    kind: u32,
}

// Extend the existing TypeTag (and existing type_children table), rather than
// introducing a recursive Type/Row serializer. Structural roots are tagged:
// Variable(TypeVariableIdentity); Application; Forall { parameters: Slice };
// EffectfulFunction; ArgumentType; ArgumentRow;
// Instance(EffectIdentity); Row { known: u32, tail: Option<TypeVariableIdentity> }.
// Application has 2 Type children. Forall has 1 Type child. EffectfulFunction has
// domain Type, result Type and Row children. Argument tags each have 1 child of
// the specified kind. Instance children are the full ordered Argument vector.
// Row children are its known Instance roots followed by its lacks Instance roots;
// known is their split index, and no-tail rows must have no lacks. Inference IDs,
// resource types and non-closed executable requests remain explicit refusals.
// Encoder and decoder use ONE heterogeneous iterative task stack across these
// roots, with the same Core payload-depth bound and fallible guarded result stack.

#[derive(Clone, Copy, Debug)]
struct NominalParameterRecord {
    owner: NominalId,
    parameters: Slice,
}

#[derive(Clone, Copy, Debug)]
struct AbstractNominalRecord {
    id: NominalId,
    spelling: Slice,
    kind: u32,
    origin: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
enum ProvenanceRecord {
    Resource {
        span: SpanRecord,
        resource: ResourceIdentity,
        arguments: Slice,
    },
    Fact(SpanRecord),
    Tuple {
        span: SpanRecord,
        elements: Slice,
    },
    Function {
        span: SpanRecord,
        domain: u32,
        codomain: u32,
        effect_arguments: Slice,
    },
    Application {
        span: SpanRecord,
        function: u32,
        argument: u32,
        argument_span: SpanRecord,
    },
    Row {
        span: SpanRecord,
        arguments: Slice,
    },
}

#[derive(Clone, Copy, Debug)]
struct ResolvedTypeRecord {
    ty: u32,
    provenance: u32,
    origin: u32,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct GlobalParameterRowRecord {
    owner: BinderIdentity,
    parameters: Slice,
}

#[derive(Clone, Copy, Debug)]
struct EffectDeclarationRecord {
    id: EffectIdentity,
    public: bool,
    spelling: Slice,
    parameters: Slice,
    operations: Slice,
    origin: u32,
    span: SpanRecord,
    native_symbol: Option<u32>,
}

#[derive(Clone, Copy, Debug)]
struct EffectOperationRecord {
    id: OperationIdentity,
    spelling: Slice,
    annotation: ResolvedTypeRecord,
    origin: u32,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedSymbolRecord {
    member_index: u32,
    name: Slice,
    native_name: Slice,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedLibraryRecord {
    module: u32,
    name: Slice,
    public: bool,
    symbols: Slice,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct NativeSymbolRecord {
    prepared_library: u32,
    library_ordinal: u32,
    symbol_index: u32,
    operation: OperationIdentity,
}

#[derive(Clone, Copy, Debug)]
struct NativeInterpretationRecord {
    effect: u32,
    symbol: u32,
}

// Extend existing NodeTag with:
// Request { effect: u32, operation: OperationIdentity, operand: u32 };
// NativeInterpret { body: u32, interpretations: Slice };
// TypeAbstraction { parameters: Slice, body: u32 };
// TypeApplication { function: u32, arguments: Slice, row_arguments: Slice }.
// Each NodeRecord gains effects: Option<u32>. The program carrier gains an
// explicit Pure/Effect dialect tag. Pure records require None; Effect records
// require Some(Row root), including empty rows. Reject mixed claims. Reuse the
// current pure feature encoder and generic CoreBuilder APIs for ordinary nodes.

wire_struct!(EffectIdentity, module, local);
wire_struct!(OperationIdentity, owner, local);
wire_struct!(ParameterRecord, id, spelling, kind, origin);
wire_struct!(QuantifierRecord, id, kind);
wire_struct!(NominalParameterRecord, owner, parameters);
wire_struct!(GlobalParameterRowRecord, owner, parameters);
wire_struct!(AbstractNominalRecord, id, spelling, kind, origin);
wire_struct!(ResolvedTypeRecord, ty, provenance, origin, span);
wire_struct!(
    EffectDeclarationRecord,
    id,
    public,
    spelling,
    parameters,
    operations,
    origin,
    span,
    native_symbol
);
wire_struct!(
    EffectOperationRecord,
    id,
    spelling,
    annotation,
    origin,
    span
);

wire_struct!(PreparedSymbolRecord, member_index, name, native_name, span);
wire_struct!(PreparedLibraryRecord, module, name, public, symbols, span);
wire_struct!(
    NativeSymbolRecord,
    prepared_library,
    library_ordinal,
    symbol_index,
    operation
);

wire_struct!(NativeInterpretationRecord, effect, symbol);

impl Wire for u64 {
    const MINIMUM: usize = 8;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        writer.bytes(&self.to_le_bytes())
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        Ok(Self::from_le_bytes(reader.array()?))
    }
}

impl Wire for ModuleRoleRecord {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Ordinary => 0u8,
            Self::BuiltinForeign => 1,
            Self::BuiltinCell => 2,
            Self::BuiltinString => 3,
            Self::BuiltinBytes => 4,
            Self::BuiltinGenericCell => 5,
            Self::BuiltinRegion => 6,
            Self::BuiltinRegionFacade => 7,
        }
        .write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Ordinary),
            1 => Ok(Self::BuiltinForeign),
            2 => Ok(Self::BuiltinCell),
            3 => Ok(Self::BuiltinString),
            4 => Ok(Self::BuiltinBytes),
            5 => Ok(Self::BuiltinGenericCell),
            6 => Ok(Self::BuiltinRegion),
            7 => Ok(Self::BuiltinRegionFacade),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for TypeVariableIdentity {
    const MINIMUM: usize = 1 + u32::MINIMUM;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Resolved { module, local } => {
                0u8.write(writer)?;
                module.write(writer)?;
                local.write(writer)
            }
            Self::Generated(local) => {
                1u8.write(writer)?;
                local.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Resolved {
                module: Wire::read(reader)?,
                local: Wire::read(reader)?,
            }),
            1 => Ok(Self::Generated(Wire::read(reader)?)),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for KindRecord {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Type => 0u8.write(writer),
            Self::EffectRow => 1u8.write(writer),
            Self::Function { domain, codomain } => {
                2u8.write(writer)?;
                domain.write(writer)?;
                codomain.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Type),
            1 => Ok(Self::EffectRow),
            2 => Ok(Self::Function {
                domain: Wire::read(reader)?,
                codomain: Wire::read(reader)?,
            }),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for ProvenanceRecord {
    const MINIMUM: usize = 1 + SpanRecord::MINIMUM;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Resource {
                span,
                resource,
                arguments,
            } => {
                5u8.write(writer)?;
                span.write(writer)?;
                resource.write(writer)?;
                arguments.write(writer)
            }
            Self::Fact(span) => {
                0u8.write(writer)?;
                span.write(writer)
            }
            Self::Tuple { span, elements } => {
                1u8.write(writer)?;
                span.write(writer)?;
                elements.write(writer)
            }
            Self::Function {
                span,
                domain,
                codomain,
                effect_arguments,
            } => {
                2u8.write(writer)?;
                span.write(writer)?;
                domain.write(writer)?;
                codomain.write(writer)?;
                effect_arguments.write(writer)
            }
            Self::Application {
                span,
                function,
                argument,
                argument_span,
            } => {
                3u8.write(writer)?;
                span.write(writer)?;
                function.write(writer)?;
                argument.write(writer)?;
                argument_span.write(writer)
            }
            Self::Row { span, arguments } => {
                4u8.write(writer)?;
                span.write(writer)?;
                arguments.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            5 => Ok(Self::Resource {
                span: Wire::read(reader)?,
                resource: Wire::read(reader)?,
                arguments: Wire::read(reader)?,
            }),
            0 => Ok(Self::Fact(Wire::read(reader)?)),
            1 => Ok(Self::Tuple {
                span: Wire::read(reader)?,
                elements: Wire::read(reader)?,
            }),
            2 => Ok(Self::Function {
                span: Wire::read(reader)?,
                domain: Wire::read(reader)?,
                codomain: Wire::read(reader)?,
                effect_arguments: Wire::read(reader)?,
            }),
            3 => Ok(Self::Application {
                span: Wire::read(reader)?,
                function: Wire::read(reader)?,
                argument: Wire::read(reader)?,
                argument_span: Wire::read(reader)?,
            }),
            4 => Ok(Self::Row {
                span: Wire::read(reader)?,
                arguments: Wire::read(reader)?,
            }),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

// Extend the existing Encoder/Decoder. The common heterogeneous stack handles
// Type -> Row -> Instance -> Argument -> Type cycles of representation without
// following the host call stack. All produced tables are compiler-private.
#[derive(Clone, Copy)]
enum StructuralInput<'a> {
    Type(&'a Type),
    Row(&'a crate::types::EffectRow),
    Instance(&'a crate::types::EffectInstance),
    Argument(&'a crate::types::KindedArgument),
}

#[path = "image_row_order.rs"]
mod row_order;

// Match Core's Type depth, not the number of private wire records. Row,
// instance and argument wrappers are metadata; Types reached through them
// inherit their enclosing depth. A unary application's function spine records
// source width, while its argument adds one structural level. EffectfulFunction
// adds one before both value children and Types nested anywhere in its row.
fn structural_child_depth(tag: TypeTag, child: usize, depth: usize) -> usize {
    match tag {
        TypeTag::ArgumentType
        | TypeTag::ArgumentRow
        | TypeTag::Instance(_)
        | TypeTag::Row { .. } => depth,
        TypeTag::Application if child == 0 => depth,
        _ => depth.saturating_add(1),
    }
}

impl Encoder<'_> {
    fn type_variable(
        &mut self,
        id: crate::types::TypeVariableId,
    ) -> Result<TypeVariableIdentity, ImageFailure> {
        charge(self.work, 1)?;
        Ok(match id {
            crate::types::TypeVariableId::Resolved { module, local } => {
                TypeVariableIdentity::Resolved {
                    module: self.module(module)?,
                    local,
                }
            }
            crate::types::TypeVariableId::Generated(local) => {
                TypeVariableIdentity::Generated(local)
            }
        })
    }

    fn effect_identity(
        &mut self,
        id: crate::types::EffectId,
    ) -> Result<EffectIdentity, ImageFailure> {
        Ok(EffectIdentity {
            module: self.module(id.module())?,
            local: id.declaration(),
        })
    }

    fn encode_kind(&mut self, root: &crate::types::Kind) -> Result<u32, ImageFailure> {
        enum Task<'a> {
            Visit(&'a crate::types::Kind, usize),
            Finish,
        }
        let mut tasks = Vec::new();
        let mut results = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(kind, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    match kind {
                        crate::types::Kind::Type | crate::types::Kind::EffectRow => {
                            let tag = if matches!(kind, crate::types::Kind::Type) {
                                KindRecord::Type
                            } else {
                                KindRecord::EffectRow
                            };
                            let slot = self.intern_kind(tag)?;
                            push(&mut results, slot, self.work)?;
                        }
                        crate::types::Kind::Arrow(domain, codomain) => {
                            push(&mut tasks, Task::Finish, self.work)?;
                            push(&mut tasks, Task::Visit(codomain, depth + 1), self.work)?;
                            push(&mut tasks, Task::Visit(domain, depth + 1), self.work)?;
                        }
                    }
                }
                Task::Finish => {
                    let codomain = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                    let domain = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                    let slot = self.intern_kind(KindRecord::Function { domain, codomain })?;
                    push(&mut results, slot, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    fn intern_kind(&mut self, record: KindRecord) -> Result<u32, ImageFailure> {
        // Flat exact representation only. encode_kind still visits every input
        // Kind and enforces the structural depth bound before reaching here.
        charge(self.work, 1)?;
        if let Some(slot) = self.kind_records.get(&record) {
            return Ok(*slot);
        }
        charge(self.work, 1)?;
        self.kind_records
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let slot = push(&mut self.image.kinds, record, self.work)?;
        self.kind_records.insert(record, slot);
        Ok(slot)
    }

    fn encode_quantifiers(
        &mut self,
        parameters: &[(crate::types::TypeVariableId, crate::types::Kind)],
    ) -> Result<Slice, ImageFailure> {
        let mut records = Vec::new();
        for (id, kind) in parameters {
            charge(self.work, 1)?;
            let id = self.type_variable(*id)?;
            let kind = self.encode_kind(kind)?;
            push(&mut records, QuantifierRecord { id, kind }, self.work)?;
        }
        // Full original variable identity, order and canonical Kind coordinates
        // are the key. This retains no typed admission or binder-scope proof.
        let lookup = records
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(1))
            .ok_or(ImageFailure::Resource)?;
        charge(self.work, lookup)?;
        if let Some(range) = self.quantifier_vectors.get(records.as_slice()) {
            return Ok(*range);
        }
        charge(self.work, lookup)?;
        self.quantifier_vectors
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let range = append(&mut self.image.quantifiers, &records, self.work)?;
        self.quantifier_vectors
            .insert(records.into_boxed_slice(), range);
        Ok(range)
    }

    // Keys contain only exact tags and canonical child slots. Hashing and
    // comparison never traverse owned Type/row trees or source allocations.
    fn intern_structural(&mut self, tag: TypeTag, children: &[u32]) -> Result<u32, ImageFailure> {
        let key_work = children
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(1))
            .ok_or(ImageFailure::Resource)?;
        charge(self.work, key_work)?;
        let probe = StructuralProbe(tag, children);
        let view: &(dyn StructuralKeyView + '_) = &probe;
        if let Some(slot) = self.structural.get(view) {
            return Ok(*slot);
        }
        // Only a miss retains a key. Pay its fallible storage and copy before
        // publishing any record; hits still pay the complete hash/Eq lookup.
        charge(self.work, children.len())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(children.len())
            .map_err(|_| ImageFailure::Resource)?;
        retained.extend_from_slice(children);
        let key = StructuralKey(tag, retained.into_boxed_slice());
        charge(self.work, key_work)?;
        self.structural
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let children = append(&mut self.image.type_children, &key.1, self.work)?;
        let slot = push(
            &mut self.image.types,
            TypeRecord { tag, children },
            self.work,
        )?;
        self.structural.insert(key, slot);
        Ok(slot)
    }

    fn encode_structural(&mut self, root: StructuralInput<'_>) -> Result<u32, ImageFailure> {
        enum Task<'a> {
            Visit(StructuralInput<'a>, usize),
            Finish(TypeTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(input, depth) => {
                    if !self.image.effect_dialect
                        && !matches!(
                            input,
                            StructuralInput::Type(
                                Type::Int
                                    | Type::Bool
                                    | Type::Unit
                                    | Type::Bytes
                                    | Type::String
                                    | Type::Nominal(_)
                                    | Type::Function(_, _)
                                    | Type::Tuple(_)
                                    | Type::Application(_, _)
                            )
                        )
                    {
                        return Err(ImageFailure::Unsupported(Unsupported::Type));
                    }
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let (tag, count) = match input {
                        StructuralInput::Type(ty) => match ty {
                            Type::Inference(_) => {
                                return Err(ImageFailure::Unsupported(Unsupported::Type));
                            }
                            Type::Int => (TypeTag::Int, 0),
                            Type::Bool => (TypeTag::Bool, 0),
                            Type::Unit => (TypeTag::Unit, 0),
                            Type::Bytes => (TypeTag::Bytes, 0),
                            Type::String => (TypeTag::String, 0),
                            Type::Nominal(id) => (TypeTag::Nominal(self.nominal(*id)?), 0),
                            Type::Variable(id) => (TypeTag::Variable(self.type_variable(*id)?), 0),
                            Type::Function(_, _) => (TypeTag::Function, 2),
                            Type::Application(_, _) => (TypeTag::Application, 2),
                            Type::Tuple(elements) => (TypeTag::Tuple, elements.len()),
                            Type::EffectfulFunction(_, _) => (TypeTag::EffectfulFunction, 3),
                            Type::Forall(parameters, _) => (
                                TypeTag::Forall {
                                    parameters: self.encode_quantifiers(parameters)?,
                                },
                                1,
                            ),

                            Type::ResourceApply(id, arguments) => (
                                TypeTag::Resource(self.resource_identity(*id)?),
                                arguments.len(),
                            ),
                        },
                        StructuralInput::Argument(argument) => match argument {
                            crate::types::KindedArgument::TypeArg(_) => (TypeTag::ArgumentType, 1),
                            crate::types::KindedArgument::RowArg(_) => (TypeTag::ArgumentRow, 1),
                        },
                        StructuralInput::Instance(instance) => (
                            TypeTag::Instance(self.effect_identity(instance.effect())?),
                            instance.arguments().len(),
                        ),
                        StructuralInput::Row(row) => {
                            let known = index(row.known().len())?;
                            let (tag, lacks) = match row.tail() {
                                Some(tail) => match tail.variable() {
                                    crate::types::EffectRowVariable::Inference(_) => {
                                        return Err(ImageFailure::Unsupported(Unsupported::Type));
                                    }
                                    crate::types::EffectRowVariable::Rigid(id) => (
                                        TypeTag::Row {
                                            known,
                                            tail: Some(self.type_variable(id)?),
                                        },
                                        tail.lacks().len(),
                                    ),
                                },
                                None => (TypeTag::Row { known, tail: None }, 0),
                            };
                            (
                                tag,
                                row.known()
                                    .len()
                                    .checked_add(lacks)
                                    .ok_or(ImageFailure::Resource)?,
                            )
                        }
                    };
                    push(&mut tasks, Task::Finish(tag, count), self.work)?;
                    charge(self.work, count)?;
                    match input {
                        StructuralInput::Type(ty) => match ty {
                            Type::Function(left, right) | Type::Application(left, right) => {
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Type(right),
                                        structural_child_depth(tag, 1, depth),
                                    ),
                                    self.work,
                                )?;
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Type(left),
                                        structural_child_depth(tag, 0, depth),
                                    ),
                                    self.work,
                                )?;
                            }
                            Type::EffectfulFunction(domain, result) => {
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Row(result.effects()),
                                        structural_child_depth(tag, 2, depth),
                                    ),
                                    self.work,
                                )?;
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Type(result.value()),
                                        structural_child_depth(tag, 1, depth),
                                    ),
                                    self.work,
                                )?;
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Type(domain),
                                        structural_child_depth(tag, 0, depth),
                                    ),
                                    self.work,
                                )?;
                            }
                            Type::Forall(_, body) => {
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Type(body),
                                        structural_child_depth(tag, 0, depth),
                                    ),
                                    self.work,
                                )?;
                            }

                            Type::ResourceApply(_, arguments) => {
                                for argument in arguments.iter().rev() {
                                    push(
                                        &mut tasks,
                                        Task::Visit(
                                            StructuralInput::Argument(argument),
                                            structural_child_depth(tag, 0, depth),
                                        ),
                                        self.work,
                                    )?;
                                }
                            }
                            Type::Tuple(elements) => {
                                for element in elements.iter().rev() {
                                    push(
                                        &mut tasks,
                                        Task::Visit(
                                            StructuralInput::Type(element),
                                            structural_child_depth(tag, 0, depth),
                                        ),
                                        self.work,
                                    )?;
                                }
                            }
                            _ => {}
                        },
                        StructuralInput::Argument(argument) => {
                            let child = match argument {
                                crate::types::KindedArgument::TypeArg(ty) => {
                                    StructuralInput::Type(ty)
                                }
                                crate::types::KindedArgument::RowArg(row) => {
                                    StructuralInput::Row(row)
                                }
                            };
                            push(
                                &mut tasks,
                                Task::Visit(child, structural_child_depth(tag, 0, depth)),
                                self.work,
                            )?;
                        }
                        StructuralInput::Instance(instance) => {
                            for argument in instance.arguments().iter().rev() {
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Argument(argument),
                                        structural_child_depth(tag, 0, depth),
                                    ),
                                    self.work,
                                )?;
                            }
                        }
                        StructuralInput::Row(row) => {
                            for instance in self.portable_row_members(row, depth)?.into_iter().rev()
                            {
                                push(
                                    &mut tasks,
                                    Task::Visit(
                                        StructuralInput::Instance(instance),
                                        structural_child_depth(tag, 0, depth),
                                    ),
                                    self.work,
                                )?;
                            }
                        }
                    }
                }
                Task::Finish(tag, count) => {
                    let start = results
                        .len()
                        .checked_sub(count)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    let slot = self.intern_structural(tag, &results[start..])?;
                    results.truncate(start);
                    push(&mut results, slot, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }
}

// Type alone has no iterative Drop; its owned variants are guarded. Rows and
// EffectInstances own iterative Drop already. The argument wrapper supplies the
// corresponding protocol before it is moved into its final instance owner.
struct ArgumentOwner(Option<crate::types::KindedArgument>);
impl ArgumentOwner {
    fn into_inner(mut self) -> crate::types::KindedArgument {
        self.0.take().expect("owned argument is live")
    }
}
impl Drop for ArgumentOwner {
    fn drop(&mut self) {
        if let Some(argument) = self.0.take() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

// A whole destination allocation remains guarded until its final typed owner
// is ready. No intermediate vector is needed to protect a partial conversion.
struct ArgumentBuffer(Vec<crate::types::KindedArgument>);
impl ArgumentBuffer {
    fn into_vec(mut self) -> Vec<crate::types::KindedArgument> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for ArgumentBuffer {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}

enum StructuralOwner {
    Type(IterativeTypeOwner),
    Row(crate::types::EffectRow),
    Instance(crate::types::EffectInstance),
    Argument(ArgumentOwner),
}
impl StructuralOwner {
    fn ty(self) -> Result<IterativeTypeOwner, ImageFailure> {
        match self {
            Self::Type(ty) => Ok(ty),
            _ => Err(ImageFailure::InvalidRecord),
        }
    }
    fn row(self) -> Result<crate::types::EffectRow, ImageFailure> {
        match self {
            Self::Row(row) => Ok(row),
            _ => Err(ImageFailure::InvalidRecord),
        }
    }
    fn instance(self) -> Result<crate::types::EffectInstance, ImageFailure> {
        match self {
            Self::Instance(instance) => Ok(instance),
            _ => Err(ImageFailure::InvalidRecord),
        }
    }
    fn argument(self) -> Result<ArgumentOwner, ImageFailure> {
        match self {
            Self::Argument(argument) => Ok(argument),
            _ => Err(ImageFailure::InvalidRecord),
        }
    }
}

impl Decoder<'_> {
    fn type_variable(
        &mut self,
        id: TypeVariableIdentity,
    ) -> Result<crate::types::TypeVariableId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(match id {
            TypeVariableIdentity::Resolved { module, local } => {
                crate::types::TypeVariableId::resolved(*get(&self.modules, module)?, local)
            }
            TypeVariableIdentity::Generated(local) => {
                crate::types::TypeVariableId::generated(local)
            }
        })
    }

    fn effect_identity(
        &mut self,
        id: EffectIdentity,
    ) -> Result<crate::types::EffectId, ImageFailure> {
        charge(self.work, 1)?;
        Ok(crate::types::EffectId::new(
            *get(&self.modules, id.module)?,
            id.local,
        ))
    }

    fn kind(&mut self, root: u32) -> Result<crate::types::Kind, ImageFailure> {
        enum Task {
            Visit(u32, usize),
            Finish,
        }
        let mut tasks = Vec::new();
        let mut results = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(slot, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    match *get(self.fact_table(&self.image.kinds, |p| p.kinds)?, slot)? {
                        KindRecord::Type => {
                            push(&mut results, crate::types::Kind::Type, self.work)?;
                        }
                        KindRecord::EffectRow => {
                            push(&mut results, crate::types::Kind::EffectRow, self.work)?;
                        }
                        KindRecord::Function { domain, codomain } => {
                            if domain >= slot || codomain >= slot {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            push(&mut tasks, Task::Finish, self.work)?;
                            push(&mut tasks, Task::Visit(codomain, depth + 1), self.work)?;
                            push(&mut tasks, Task::Visit(domain, depth + 1), self.work)?;
                        }
                    }
                }
                Task::Finish => {
                    let codomain = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                    let domain = results.pop().ok_or(ImageFailure::InvalidRecord)?;
                    push(
                        &mut results,
                        crate::types::Kind::Arrow(Box::new(domain), Box::new(codomain)),
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

    fn structural(&mut self, root: u32) -> Result<StructuralOwner, ImageFailure> {
        self.structural_with_depth(root).map(|(value, _)| value)
    }

    fn structural_with_depth(
        &mut self,
        root: u32,
    ) -> Result<(StructuralOwner, usize), ImageFailure> {
        enum Task {
            Visit(u32, usize),
            Finish(TypeTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results: Vec<StructuralOwner> = Vec::new();
        let mut maximum_depth = 0;
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(slot, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    maximum_depth = maximum_depth.max(depth);
                    if self.expected_fact_prefixes.is_none() {
                        let key = (slot, self.sources.len(), self.modules.len());
                        charge(self.work, 1)?;
                        if let Some(cached) = self.decoded_types.get(&key) {
                            let complete_depth = depth
                                .checked_add(cached.depth)
                                .ok_or(ImageFailure::Resource)?;
                            if complete_depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                                return Err(ImageFailure::Resource);
                            }
                            maximum_depth = maximum_depth.max(complete_depth);
                            let ty = crate::types::clone_type_with_budget(&cached.value, self.work)
                                .map(IterativeTypeOwner::new)
                                .map_err(|()| ImageFailure::Resource)?;
                            push(&mut results, StructuralOwner::Type(ty), self.work)?;
                            continue;
                        }
                    }
                    let record = *get(self.fact_table(&self.image.types, |p| p.types)?, slot)?;
                    if self.expected_fact_prefixes.is_none()
                        && matches!(record.tag, TypeTag::Row { .. })
                    {
                        charge(self.work, 1)?;
                        if let Some(row) =
                            self.decoded_rows
                                .get(&(slot, self.sources.len(), self.modules.len()))
                        {
                            let complete_depth =
                                depth.checked_add(row.depth).ok_or(ImageFailure::Resource)?;
                            if complete_depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                                return Err(ImageFailure::Resource);
                            }
                            maximum_depth = maximum_depth.max(complete_depth);
                            let value =
                                crate::types::clone_effect_row_with_budget(&row.value, self.work)
                                    .map_err(|()| ImageFailure::Resource)?;
                            push(&mut results, StructuralOwner::Row(value), self.work)?;
                            continue;
                        }
                    }
                    if !self.image.effect_dialect
                        && !matches!(
                            record.tag,
                            TypeTag::Int
                                | TypeTag::Bool
                                | TypeTag::Unit
                                | TypeTag::Bytes
                                | TypeTag::String
                                | TypeTag::Nominal(_)
                                | TypeTag::Function
                                | TypeTag::Tuple
                                | TypeTag::Application
                        )
                        && !matches!(record.tag, TypeTag::Variable(TypeVariableIdentity::Resolved { module, .. })
                            if get(&self.modules, module).is_ok_and(|module| module.is_builtin_foreign()))
                    {
                        return Err(ImageFailure::Unsupported(Unsupported::Type));
                    }
                    let children = record
                        .children
                        .get(self.fact_table(&self.image.type_children, |p| p.type_children)?)?;
                    let count = children.len();
                    let valid = match record.tag {
                        TypeTag::Function | TypeTag::Application => count == 2,
                        TypeTag::EffectfulFunction => count == 3,
                        TypeTag::Forall { .. } | TypeTag::ArgumentType | TypeTag::ArgumentRow => {
                            count == 1
                        }
                        TypeTag::Tuple => count >= 2,
                        TypeTag::Instance(_) | TypeTag::Resource(_) => true,

                        TypeTag::Row { known, tail } => usize::try_from(known).is_ok_and(|known| {
                            known <= count && (tail.is_some() || known == count)
                        }),
                        _ => count == 0,
                    };
                    if !valid {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    push(&mut tasks, Task::Finish(record.tag, count), self.work)?;
                    charge(self.work, count)?;
                    for (position, child) in children.iter().enumerate().rev() {
                        if *child >= slot {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        push(
                            &mut tasks,
                            Task::Visit(
                                *child,
                                structural_child_depth(record.tag, position, depth),
                            ),
                            self.work,
                        )?;
                    }
                }
                Task::Finish(tag, count) => {
                    // All children remain individually guarded through every
                    // tag/shape/reservation failure, including heterogeneous ones.
                    let result = match tag {
                        TypeTag::ArgumentType => StructuralOwner::Argument(ArgumentOwner(Some(
                            crate::types::KindedArgument::TypeArg(
                                results
                                    .pop()
                                    .ok_or(ImageFailure::InvalidRecord)?
                                    .ty()?
                                    .into_inner(),
                            ),
                        ))),
                        TypeTag::ArgumentRow => StructuralOwner::Argument(ArgumentOwner(Some(
                            crate::types::KindedArgument::RowArg(
                                results.pop().ok_or(ImageFailure::InvalidRecord)?.row()?,
                            ),
                        ))),
                        TypeTag::Instance(id) => {
                            let id = self.effect_identity(id)?;
                            let start = results
                                .len()
                                .checked_sub(count)
                                .ok_or(ImageFailure::InvalidRecord)?;
                            charge(self.work, count)?;
                            let mut owned = ArgumentBuffer(Vec::new());
                            owned
                                .0
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            // The final allocation guards all extracted arguments,
                            // including when a later child has the wrong shape.
                            for child in results.drain(start..) {
                                owned.0.push(child.argument()?.into_inner());
                            }
                            StructuralOwner::Instance(crate::types::EffectInstance::new_kinded(
                                id,
                                owned.into_vec().into_boxed_slice(),
                            ))
                        }

                        TypeTag::Row { known, tail } => {
                            let known =
                                usize::try_from(known).map_err(|_| ImageFailure::InvalidRecord)?;
                            let start = results
                                .len()
                                .checked_sub(count)
                                .ok_or(ImageFailure::InvalidRecord)?;
                            let mut instances = Vec::new();
                            charge(self.work, count)?;
                            instances
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            for child in results.drain(start..) {
                                instances.push(child.instance()?);
                            }
                            let mut lacks = Vec::new();
                            charge(
                                self.work,
                                count
                                    .checked_sub(known)
                                    .ok_or(ImageFailure::InvalidRecord)?,
                            )?;
                            lacks
                                .try_reserve_exact(count - known)
                                .map_err(|_| ImageFailure::Resource)?;
                            lacks.extend(instances.drain(known..));
                            let tail = match tail {
                                Some(id) => Some((
                                    crate::types::EffectRowVariable::Rigid(self.type_variable(id)?),
                                    lacks,
                                )),
                                None if lacks.is_empty() => None,
                                _ => return Err(ImageFailure::InvalidRecord),
                            };
                            let row = crate::types::effect_row_from_owned_parts_with_budget(
                                instances, tail, self.work,
                            )
                            .map_err(|()| ImageFailure::Resource)?;
                            StructuralOwner::Row(row)
                        }

                        tag => {
                            let ty = match tag {
                                TypeTag::Resource(id) => {
                                    let id = self.resource_identity(id)?;
                                    let start = results
                                        .len()
                                        .checked_sub(count)
                                        .ok_or(ImageFailure::InvalidRecord)?;
                                    let mut owned = ArgumentBuffer(Vec::new());
                                    charge(self.work, count)?;
                                    owned
                                        .0
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for child in results.drain(start..) {
                                        owned.0.push(child.argument()?.into_inner());
                                    }
                                    Type::ResourceApply(id, owned.into_vec().into_boxed_slice())
                                }

                                TypeTag::Int => Type::Int,
                                TypeTag::Bool => Type::Bool,
                                TypeTag::Unit => Type::Unit,
                                TypeTag::Bytes => Type::Bytes,
                                TypeTag::String => Type::String,
                                TypeTag::Nominal(id) => Type::Nominal(self.nominal(id)?),
                                TypeTag::Variable(id) => Type::Variable(self.type_variable(id)?),
                                TypeTag::Function | TypeTag::Application => {
                                    let right =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    let left =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    let left = Box::new(left.into_inner());
                                    let right = Box::new(right.into_inner());
                                    if matches!(tag, TypeTag::Function) {
                                        Type::Function(left, right)
                                    } else {
                                        Type::Application(left, right)
                                    }
                                }
                                TypeTag::EffectfulFunction => {
                                    let row =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.row()?;
                                    let value =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    let domain =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    Type::EffectfulFunction(
                                        Box::new(domain.into_inner()),
                                        Box::new(crate::types::ComputationType::new(
                                            value.into_inner(),
                                            row,
                                        )),
                                    )
                                }
                                TypeTag::Tuple => {
                                    let start = results
                                        .len()
                                        .checked_sub(count)
                                        .ok_or(ImageFailure::InvalidRecord)?;
                                    let mut owned = TypeBuffer(Vec::new());
                                    charge(self.work, count)?;
                                    owned
                                        .0
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for child in results.drain(start..) {
                                        owned.0.push(child.ty()?.into_inner());
                                    }
                                    Type::Tuple(owned.into_vec().into_boxed_slice())
                                }
                                TypeTag::Forall { parameters } => {
                                    let body =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    let records = parameters.get(
                                        self.fact_table(&self.image.quantifiers, |p| {
                                            p.quantifiers
                                        })?,
                                    )?;
                                    if records.is_empty() {
                                        return Err(ImageFailure::InvalidRecord);
                                    }
                                    let mut parameters = Vec::new();
                                    charge(self.work, records.len())?;
                                    parameters
                                        .try_reserve_exact(records.len())
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for record in records {
                                        parameters.push((
                                            self.type_variable(record.id)?,
                                            self.kind(record.kind)?,
                                        ));
                                    }
                                    Type::Forall(
                                        parameters.into_boxed_slice(),
                                        Box::new(body.into_inner()),
                                    )
                                }
                                _ => return Err(ImageFailure::InvalidRecord),
                            };
                            StructuralOwner::Type(IterativeTypeOwner::new(ty))
                        }
                    };
                    push(&mut results, result, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .map(|value| (value, maximum_depth))
            .ok_or(ImageFailure::InvalidRecord)
    }
}

// Additional Encoder state:
// prepared_libraries: HashMap<*const PreparedForeignLibrary, u32>,
// native_symbols: HashMap<OperationId, (*const CheckedForeignSymbol, u32)>,
// call_codecs: HashMap<*const CheckedForeignCallCodec, u32>.
// Reserve each entry fallibly and precharge before every lookup/insert.

impl Encoder<'_> {
    // Scalar imports retain these passive schemes without authorizing pure
    // byte applications or general polymorphic executable images.

    fn operation_identity(
        &mut self,
        id: crate::types::OperationId,
    ) -> Result<OperationIdentity, ImageFailure> {
        Ok(OperationIdentity {
            owner: self.effect_identity(id.owner())?,
            local: id.operation(),
        })
    }

    fn prepared_span(&mut self, origin: &Origin) -> Result<SpanRecord, ImageFailure> {
        match origin {
            Origin::Source(span) => self.span(*span),
            _ => Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata)),
        }
    }

    fn encode_prepared_library(
        &mut self,
        original: &Arc<crate::foreign::source_contract::PreparedForeignLibrary>,
    ) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        let key = Arc::as_ptr(original);
        if let Some(slot) = self.prepared_libraries.get(&key) {
            return Ok(*slot);
        }
        charge(self.work, 1)?;
        self.prepared_libraries
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let module = self.module(original.module())?;
        let name = append(&mut self.image.bytes, original.name().as_bytes(), self.work)?;
        let span = self.prepared_span(original.origin())?;
        let start = self.image.prepared_symbols.len();
        for symbol in original.symbols() {
            let name = append(&mut self.image.bytes, symbol.name().as_bytes(), self.work)?;
            let native_name = append(
                &mut self.image.bytes,
                symbol.native_name().as_bytes(),
                self.work,
            )?;
            let span = self.prepared_span(symbol.origin())?;
            push(
                &mut self.image.prepared_symbols,
                PreparedSymbolRecord {
                    member_index: index(symbol.member_index())?,
                    name,
                    native_name,
                    span,
                },
                self.work,
            )?;
        }
        let symbols = Slice::of(&self.image.prepared_symbols, start)?;
        let slot = push(
            &mut self.image.prepared_libraries,
            PreparedLibraryRecord {
                module,
                name,
                public: original.public(),
                symbols,
                span,
            },
            self.work,
        )?;
        self.prepared_libraries.insert(key, slot);
        Ok(slot)
    }

    // The codec allocation is prepared once, shared by pure checks and calls.

    fn encode_native_symbol(
        &mut self,
        original: &Arc<crate::foreign::checked_source::CheckedForeignSymbol>,
    ) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        let key = original.operation();
        let pointer = Arc::as_ptr(original);
        if let Some((original_pointer, slot)) = self.native_symbols.get(&key) {
            return if *original_pointer == pointer {
                Ok(*slot)
            } else {
                Err(ImageFailure::InvalidRecord)
            };
        }
        charge(self.work, 1)?;
        self.native_symbols
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let prepared_library = self.encode_prepared_library(original.prepared())?;
        let operation = self.operation_identity(original.operation())?;
        let slot = push(
            &mut self.image.native_symbols,
            NativeSymbolRecord {
                prepared_library,
                library_ordinal: original.library().ordinal(),
                symbol_index: index(original.symbol_index())?,
                operation,
            },
            self.work,
        )?;
        charge(self.work, 1)?; // Arc sharing is preparation work; no new descriptor allocation.
        let original_slot = push(
            &mut self.original_native_symbols,
            Arc::clone(original),
            self.work,
        )?;
        if original_slot != slot {
            return Err(ImageFailure::InvalidRecord);
        }
        self.native_symbols.insert(key, (pointer, slot));
        Ok(slot)
    }

    fn encode_parameter(
        &mut self,
        original: &crate::resolved::ResolvedTypeVariable,
    ) -> Result<u32, ImageFailure> {
        // Existing canonical registry constructors retain source parameters via
        // an older Origin clone seam. Keep this first image subset explicitly
        // Source-only here rather than passing a recursive Origin through it.
        if !matches!(original.origin, Origin::Source(_)) {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        self.encode_parameter_data(original)
    }

    // Global records are consumed by their owning registry helper, so recursive
    // origins can use the existing paid flat Origin codec without cloning.
    fn encode_parameter_data(
        &mut self,
        original: &crate::resolved::ResolvedTypeVariable,
    ) -> Result<u32, ImageFailure> {
        let id = self.type_variable(original.id)?;
        let spelling = append(
            &mut self.image.bytes,
            original.spelling.as_bytes(),
            self.work,
        )?;
        let kind = self.encode_kind(&original.kind)?;
        let origin = self.encode_origin(&original.origin)?;
        push(
            &mut self.image.parameters,
            ParameterRecord {
                id,
                spelling,
                kind,
                origin,
            },
            self.work,
        )
    }

    fn encode_provenance(
        &mut self,
        original: &crate::resolved::ResolvedTypeProvenance,
    ) -> Result<u32, ImageFailure> {
        use crate::resolved::ResolvedTypeProvenanceNode as P;
        // The original is already an arena. Retain its source-order construction
        // records without recursive traversal or per-child Arc clones.
        let start = self.image.provenance.len();
        let children_start = self.image.provenance_children.len();
        charge(self.work, original.nodes().len())?;
        for (local, node) in original.nodes().iter().enumerate() {
            let root = |child: usize| -> Result<u32, ImageFailure> {
                if child >= local {
                    return Err(ImageFailure::InvalidRecord);
                }
                index(start.checked_add(child).ok_or(ImageFailure::Resource)?)
            };
            let record = match node {
                P::Fact(span) => ProvenanceRecord::Fact(self.span(*span)?),
                P::Tuple { span, elements }
                | P::Row {
                    span,
                    argument_roots: elements,
                } => {
                    let span = self.span(*span)?;
                    let child_start = self.image.provenance_children.len();
                    for child in elements.iter() {
                        push(
                            &mut self.image.provenance_children,
                            root(*child)?,
                            self.work,
                        )?;
                    }
                    let elements = Slice::of(&self.image.provenance_children, child_start)?;
                    if matches!(node, P::Tuple { .. }) {
                        ProvenanceRecord::Tuple { span, elements }
                    } else {
                        ProvenanceRecord::Row {
                            span,
                            arguments: elements,
                        }
                    }
                }
                P::Function {
                    span,
                    domain,
                    codomain,
                    effect_arguments,
                } => {
                    let span = self.span(*span)?;
                    let domain = root(*domain)?;
                    let codomain = root(*codomain)?;
                    let child_start = self.image.provenance_children.len();
                    for child in effect_arguments.iter() {
                        push(
                            &mut self.image.provenance_children,
                            root(*child)?,
                            self.work,
                        )?;
                    }
                    ProvenanceRecord::Function {
                        span,
                        domain,
                        codomain,
                        effect_arguments: Slice::of(&self.image.provenance_children, child_start)?,
                    }
                }
                P::Application {
                    span,
                    function,
                    argument,
                    argument_span,
                } => ProvenanceRecord::Application {
                    span: self.span(*span)?,
                    function: root(*function)?,
                    argument: root(*argument)?,
                    argument_span: self.span(*argument_span)?,
                },
                P::Resource {
                    span,
                    resource,
                    arguments,
                } => {
                    let span = self.span(*span)?;
                    let resource = self.resource_identity(*resource)?;
                    let start = self.image.provenance_children.len();
                    for child in arguments {
                        push(
                            &mut self.image.provenance_children,
                            root(*child)?,
                            self.work,
                        )?;
                    }
                    ProvenanceRecord::Resource {
                        span,
                        resource,
                        arguments: Slice::of(&self.image.provenance_children, start)?,
                    }
                }
            };
            push(&mut self.image.provenance, record, self.work)?;
        }
        if original.root() >= original.nodes().len() {
            return Err(ImageFailure::InvalidRecord);
        }
        let nodes = Slice::of(&self.image.provenance, start)?;
        let children = Slice::of(&self.image.provenance_children, children_start)?;
        push(
            &mut self.image.provenance_views,
            ProvenanceViewRecord {
                nodes,
                children,
                root: index(original.root())?,
            },
            self.work,
        )
    }

    fn encode_extended_registry(
        &mut self,
        registry: &ResolvedRegistry,
    ) -> Result<(), ImageFailure> {
        self.encode_interface_owners(registry)?;
        let mut nominal_parameters = Vec::new();
        for (owner, parameters) in registry.nominal_parameter_entries() {
            let key = self.nominal(owner)?;
            push(&mut nominal_parameters, (key, parameters), self.work)?;
        }
        sort_image_records(&mut nominal_parameters, |entry| entry.0, self.work)?;
        for (owner, parameters) in nominal_parameters {
            charge(self.work, 1)?;
            let start = self.image.parameters.len();
            for parameter in parameters {
                self.encode_parameter(parameter)?;
            }
            push(
                &mut self.image.nominal_parameters,
                NominalParameterRecord {
                    owner,
                    parameters: Slice::of(&self.image.parameters, start)?,
                },
                self.work,
            )?;
        }
        for row in registry.global_parameter_rows() {
            charge(self.work, 1)?;
            let owner = self.binder_id(row.owner())?;
            if !matches!(owner, BinderIdentity::Resolved { .. }) || row.parameters().is_empty() {
                return Err(ImageFailure::InvalidRecord);
            }
            let start = self.image.parameters.len();
            for identity in row.parameters() {
                charge(self.work, 1)?;
                let parameter = registry
                    .type_variable(*identity)
                    .ok_or(ImageFailure::InvalidRecord)?;
                if parameter.id != *identity {
                    return Err(ImageFailure::InvalidRecord);
                }
                self.encode_parameter_data(parameter)?;
            }
            push(
                &mut self.image.global_parameters,
                GlobalParameterRowRecord {
                    owner,
                    parameters: Slice::of(&self.image.parameters, start)?,
                },
                self.work,
            )?;
        }
        let mut abstracts = Vec::new();
        for (id, kind, origin) in registry.abstract_nominal_kind_entries() {
            let key = self.nominal(id)?;
            push(&mut abstracts, (key, id, kind, origin), self.work)?;
        }
        sort_image_records(&mut abstracts, |entry| entry.0, self.work)?;
        for (key, id, kind, origin) in abstracts {
            charge(self.work, 1)?;

            let crate::resolved::NonMaterializedNominalKind::Ordinary(kind) = kind else {
                continue; // exact source family kinds are reconstructed from their original headers
            };
            let spelling = registry
                .image_abstract_nominal_name(id)
                .ok_or(ImageFailure::InvalidRecord)?;
            let spelling = append(&mut self.image.bytes, spelling.as_bytes(), self.work)?;
            let id = key;
            let kind = self.encode_kind(kind)?;
            let origin = self.span(origin)?;
            push(
                &mut self.image.abstract_nominals,
                AbstractNominalRecord {
                    id,
                    spelling,
                    kind,
                    origin,
                },
                self.work,
            )?;
        }
        for effect in registry.effects() {
            charge(self.work, 1)?;
            let native_symbol = effect
                .native_contract
                .as_ref()
                .map(|symbol| self.encode_native_symbol(symbol))
                .transpose()?;
            let id = self.effect_identity(effect.id)?;
            let spelling = append(&mut self.image.bytes, effect.spelling.as_bytes(), self.work)?;
            let origin = self.encode_origin(&effect.origin)?;
            let span = self.span(effect.span)?;
            let start = self.image.parameters.len();
            for parameter in &effect.parameters {
                self.encode_parameter(parameter)?;
            }
            let parameters = Slice::of(&self.image.parameters, start)?;
            let start = self.image.operations.len();
            for operation in &effect.operations {
                charge(self.work, 1)?;
                let id = self.operation_identity(operation.id)?;
                let spelling = append(
                    &mut self.image.bytes,
                    operation.spelling.as_bytes(),
                    self.work,
                )?;
                let ty = self.encode_type(&operation.annotation.ty)?;
                let provenance = self.encode_provenance(&operation.annotation.provenance)?;
                let annotation_origin = self.encode_origin(&operation.annotation.origin)?;
                let annotation_span = self.span(operation.annotation.span)?;
                let origin = self.encode_origin(&operation.origin)?;
                let span = self.span(operation.span)?;
                push(
                    &mut self.image.operations,
                    EffectOperationRecord {
                        id,
                        spelling,
                        annotation: ResolvedTypeRecord {
                            ty,
                            provenance,
                            origin: annotation_origin,
                            span: annotation_span,
                        },
                        origin,
                        span,
                    },
                    self.work,
                )?;
            }
            let operations = Slice::of(&self.image.operations, start)?;
            push(
                &mut self.image.effects,
                EffectDeclarationRecord {
                    id,
                    public: effect.public,
                    spelling,
                    parameters,
                    operations,
                    origin,
                    span,
                    native_symbol,
                },
                self.work,
            )?;
        }
        let mut selected = HashMap::new();
        charge(self.work, registry.type_variable_count())?;
        selected
            .try_reserve(registry.type_variable_count())
            .map_err(|_| ImageFailure::Resource)?;
        for (_, parameters) in registry.nominal_parameter_entries() {
            for parameter in parameters {
                selected.insert(parameter.id, ());
            }
        }
        for effect in registry.effects() {
            for parameter in &effect.parameters {
                selected.insert(parameter.id, ());
            }
        }
        for row in registry.global_parameter_rows() {
            for id in row.parameters() {
                selected.insert(*id, ());
            }
        }
        for (_, parameters) in registry.image_interface_owner_definitions() {
            for parameter in parameters {
                selected.insert(parameter.id, ());
            }
        }
        // Preserve actual source Cell and region scope identities beyond
        // declaration-owned variables. The generated root owns no registry fact.
        let mut parameters = Vec::new();
        for parameter in registry.type_variables() {
            let key = self.type_variable(parameter.id)?;
            push(&mut parameters, (key, parameter), self.work)?;
        }
        sort_image_records(&mut parameters, |entry| entry.0, self.work)?;
        for (_, parameter) in parameters {
            charge(self.work, 1)?;
            if !selected.contains_key(&parameter.id) {
                let slot = self.encode_parameter(parameter)?;
                push(&mut self.image.scope_parameters, slot, self.work)?;
            }
        }
        Ok(())
    }
}
// Native-image extensions: these share the existing flat tables, wire codec,
// meter, Core builders and independent validators. No source frontend runs.
impl Encoder<'_> {
    fn encode_effect_node(
        &mut self,
        kind: &crate::core::EffectExprKind,
    ) -> Result<NodeTag, ImageFailure> {
        use crate::core::{EffectExprKind, EffectOperation};
        match kind {
            EffectExprKind::Operation(EffectOperation::RegionValueRequest(request)) => {
                Ok(NodeTag::RegionValueRequest {
                    api: self.module(request.api)?,
                    fields: index(request.fields)?,
                })
            }
            EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) => {
                use crate::core::region::RegionBufferOperation;
                let (source, module, operation, bytes) = match &buffer.operation {
                    RegionBufferOperation::IntegerLiteral(integer) => {
                        charge(
                            self.work,
                            usize::try_from(integer.magnitude_byte_length())
                                .map_err(|_| ImageFailure::Resource)?,
                        )?;
                        let (negative, bytes) = integer.sign_magnitude();
                        (
                            3,
                            None,
                            u8::from(negative),
                            append(&mut self.image.bytes, &bytes, self.work)?,
                        )
                    }
                    RegionBufferOperation::IntegerArithmetic(primitive) => {
                        let operation = match primitive {
                            crate::core::Primitive::Add => 0,
                            crate::core::Primitive::Multiply => 1,
                            _ => return Err(ImageFailure::InvalidRecord),
                        };
                        (4, None, operation, Slice { start: 0, len: 0 })
                    }
                    RegionBufferOperation::StringLiteral(bytes) => {
                        (0, None, 0, append(&mut self.image.bytes, bytes, self.work)?)
                    }
                    RegionBufferOperation::Intrinsic(intrinsic) => {
                        let tag = self
                            .encode_node(&PureExprKind::Value(PureValue::Intrinsic(*intrinsic)))?;
                        let (source, module, operation) = match tag {
                            NodeTag::BytesIntrinsic { module, operation } => (1, module, operation),
                            NodeTag::StringIntrinsic { module, operation } => {
                                (2, module, operation)
                            }
                            _ => return Err(ImageFailure::InvalidRecord),
                        };
                        (source, Some(module), operation, Slice { start: 0, len: 0 })
                    }
                };
                Ok(NodeTag::RegionBuffer {
                    api: self.module(buffer.api)?,
                    context: self.node(buffer.context)?,
                    operand: buffer.operand.map(|id| self.node(id)).transpose()?,
                    right: buffer.right.map(|id| self.node(id)).transpose()?,
                    source,
                    module,
                    operation,
                    bytes,
                })
            }
            EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) => {
                let start = self.image.node_children.len();
                for field in &tuple.fields {
                    let field = self.node(*field)?;
                    push(&mut self.image.node_children, field, self.work)?;
                }
                Ok(NodeTag::RegionTuple {
                    constructor: tuple
                        .constructor
                        .map(|id| self.constructor(id))
                        .transpose()?,
                    api: self.module(tuple.api)?,
                    context: self.node(tuple.context)?,
                    storage: self.node(tuple.storage)?,
                    fields: Slice::of(&self.image.node_children, start)?,
                })
            }
            EffectExprKind::Pure(kind) => self.encode_node(kind),
            EffectExprKind::Operation(EffectOperation::Region(scope)) => Ok(NodeTag::Region {
                entry: scope.entry,
                api: self.module(scope.api)?,
                identity: self.type_variable(scope.identity)?,
                access: self.encode_binder(&scope.access)?,
                preceding: self.node(scope.preceding)?,
                provider: self.node(scope.provider)?,
                body: self.node(scope.body)?,
            }),
            EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) => {
                Ok(NodeTag::RegionAllocate {
                    api: self.module(allocation.api)?,
                    context: self.node(allocation.context)?,
                    request: self.node(allocation.request)?,
                })
            }
            EffectExprKind::Operation(EffectOperation::Resource(scope)) => Ok(NodeTag::CellScope {
                acquisition: self.encode_cell_acquisition(scope.acquisition)?,
                handle: self.encode_binder(scope.handle())?,
                initializer: self.node(scope.initializer())?,
                body: self.node(scope.body())?,
            }),
            EffectExprKind::Operation(EffectOperation::Cleanup(scope)) => Ok(NodeTag::Cleanup {
                callback: self.binder_id(scope.callback)?,
                body: self.node(scope.body)?,
                action: self.node(scope.action)?,
                span: self.span(scope.span)?,
                action_span: self.span(scope.action_span)?,
            }),
            EffectExprKind::Operation(EffectOperation::Registration(scope)) => {
                Ok(NodeTag::Registration {
                    handler: scope.handler.value(),
                    callback: self.binder_id(scope.callback)?,
                    body: self.node(scope.body)?,
                    span: self.span(scope.span)?,
                })
            }

            EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                Ok(NodeTag::Handler(self.encode_handler(handler)?))
            }
            EffectExprKind::Operation(EffectOperation::Resume(resume)) => Ok(NodeTag::Resume {
                handler: resume.handler().value(),
                owner: resume.owner().value(),
                available: resume.use_state() == crate::core::ResumeUse::Available,
                value: self.node(resume.value())?,
            }),
            EffectExprKind::Operation(EffectOperation::Discard(discard)) => Ok(NodeTag::Discard {
                handler: discard.handler().value(),
                owner: discard.owner().value(),
                available: discard.use_state() == crate::core::ResumeUse::Available,
            }),
            EffectExprKind::Operation(EffectOperation::Request(request)) => {
                // Generic helper templates retain lexical rigid actuals. The
                // independent Core scope/kind gate checks those binders, and
                // existing runtime instantiation specializes the complete vector.
                // Only executable interpreter bindings must be closed here.
                Ok(NodeTag::Request {
                    effect: self.encode_structural(StructuralInput::Instance(request.effect()))?,
                    operation: self.operation_identity(request.operation())?,
                    operand: self.node(request.operand())?,
                })
            }
            EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) => {
                let start = self.image.interpretations.len();
                for interpretation in boundary.interpretations() {
                    charge(self.work, 1)?;
                    let effect =
                        self.encode_structural(StructuralInput::Instance(interpretation.effect()))?;
                    let symbol = self.encode_native_symbol(interpretation.symbol())?;
                    push(
                        &mut self.image.interpretations,
                        NativeInterpretationRecord { effect, symbol },
                        self.work,
                    )?;
                }
                Ok(NodeTag::NativeInterpret {
                    body: self.node(boundary.body())?,
                    interpretations: Slice::of(&self.image.interpretations, start)?,
                })
            }
        }
    }
}

// A lexical checked host is the sole permitted open actual. This restores
// representation only; final Core independently checks the binder and escape.

// Standalone intermediate buffers retain iterative ownership until transfer.
struct ParameterBuffer(Vec<crate::resolved::ResolvedTypeVariable>);
impl ParameterBuffer {
    fn into_vec(mut self) -> Vec<crate::resolved::ResolvedTypeVariable> {
        std::mem::take(&mut self.0)
    }
    fn into_boxed_slice(self) -> Box<[crate::resolved::ResolvedTypeVariable]> {
        self.into_vec().into_boxed_slice()
    }
}
impl Drop for ParameterBuffer {
    fn drop(&mut self) {
        for parameter in self.0.drain(..) {
            crate::source::discard_origin_iteratively(parameter.origin);
        }
    }
}
struct NominalParameterBuffer(Vec<(NominalTypeId, Vec<crate::resolved::ResolvedTypeVariable>)>);
impl NominalParameterBuffer {
    fn into_vec(mut self) -> Vec<(NominalTypeId, Vec<crate::resolved::ResolvedTypeVariable>)> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for NominalParameterBuffer {
    fn drop(&mut self) {
        for (_, parameters) in self.0.drain(..) {
            drop(ParameterBuffer(parameters));
        }
    }
}
struct GlobalParameterBuffer(Vec<(BinderId, Vec<crate::resolved::ResolvedTypeVariable>)>);
impl GlobalParameterBuffer {
    fn into_vec(mut self) -> Vec<(BinderId, Vec<crate::resolved::ResolvedTypeVariable>)> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for GlobalParameterBuffer {
    fn drop(&mut self) {
        for (_, parameters) in self.0.drain(..) {
            drop(ParameterBuffer(parameters));
        }
    }
}
struct TypeBuffer(Vec<Type>);
impl TypeBuffer {
    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for TypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

impl Decoder<'_> {
    fn operation_identity(
        &mut self,
        record: OperationIdentity,
    ) -> Result<crate::types::OperationId, ImageFailure> {
        Ok(crate::types::OperationId::new(
            self.effect_identity(record.owner)?,
            record.local,
        ))
    }

    fn parameter(
        &mut self,
        record: ParameterRecord,
    ) -> Result<crate::resolved::ResolvedTypeVariable, ImageFailure> {
        charge(self.work, 1)?;
        if !matches!(
            get(
                self.fact_table(&self.image.origins, |p| p.origins)?,
                record.origin
            )?,
            OriginRecord::Source(_)
        ) {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        self.parameter_data(record)
    }

    fn parameter_data(
        &mut self,
        record: ParameterRecord,
    ) -> Result<crate::resolved::ResolvedTypeVariable, ImageFailure> {
        let id = self.type_variable(record.id)?;
        let spelling = self.text(record.spelling)?;
        let kind = self.kind(record.kind)?;
        let origin = self.origin(record.origin)?;
        Ok(crate::resolved::ResolvedTypeVariable {
            id,
            spelling,
            kind,
            origin: origin.take(),
        })
    }

    fn parameters(&mut self, records: Slice) -> Result<ParameterBuffer, ImageFailure> {
        let records = records.get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?;
        let mut parameters = ParameterBuffer(Vec::new());
        charge(self.work, records.len())?;
        parameters
            .0
            .try_reserve_exact(records.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in records {
            let parameter = self.parameter(*record)?;
            parameters.0.push(parameter);
        }
        Ok(parameters)
    }

    fn global_parameters(&mut self, records: Slice) -> Result<ParameterBuffer, ImageFailure> {
        let records = records.get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?;
        let mut parameters = ParameterBuffer(Vec::new());
        charge(self.work, records.len())?;
        parameters
            .0
            .try_reserve_exact(records.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in records {
            charge(self.work, 1)?;
            let parameter = self.parameter_data(*record)?;
            parameters.0.push(parameter);
        }
        Ok(parameters)
    }

    // Restore each recorded complete arena once. Occurrence roots may share
    // only their own arena; all nodes/edges retain existing full-arena equality.
    fn provenance_arena(&mut self) -> Result<Option<RestoredProvenance>, ImageFailure> {
        use crate::resolved::ResolvedTypeProvenanceNode as P;
        charge(self.work, self.image.provenance_views.len())?;
        let mut views = Vec::new();
        views
            .try_reserve_exact(self.image.provenance_views.len())
            .map_err(|_| ImageFailure::Resource)?;
        let mut next_node = 0usize;
        let mut next_child = 0usize;
        for view in &self.image.provenance_views {
            charge(self.work, 6)?;
            let node_start =
                usize::try_from(view.nodes.start).map_err(|_| ImageFailure::InvalidRecord)?;
            let child_start =
                usize::try_from(view.children.start).map_err(|_| ImageFailure::InvalidRecord)?;
            let root = usize::try_from(view.root).map_err(|_| ImageFailure::InvalidRecord)?;
            let records = view.nodes.get(&self.image.provenance)?;
            view.children.get(&self.image.provenance_children)?;
            if node_start != next_node
                || child_start != next_child
                || records.is_empty()
                || root >= records.len()
            {
                return Err(ImageFailure::InvalidRecord);
            }
            next_node = node_start
                .checked_add(records.len())
                .ok_or(ImageFailure::Resource)?;
            let child_end_u32 = view
                .children
                .start
                .checked_add(view.children.len)
                .ok_or(ImageFailure::InvalidRecord)?;
            next_child = usize::try_from(child_end_u32).map_err(|_| ImageFailure::InvalidRecord)?;
            charge(
                self.work,
                records.len().checked_add(1).ok_or(ImageFailure::Resource)?,
            )?;
            let mut arena = Vec::new();
            arena
                .try_reserve_exact(records.len())
                .map_err(|_| ImageFailure::Resource)?;
            let mut child_cursor = view.children.start;
            for (slot, record) in records.iter().enumerate() {
                charge(self.work, 1)?;
                let root = |record: u32| -> Result<usize, ImageFailure> {
                    let root = usize::try_from(record).map_err(|_| ImageFailure::InvalidRecord)?;
                    let root = root
                        .checked_sub(node_start)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    if root >= slot {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    Ok(root)
                };
                let mut roots = |records: Slice,
                                 work: &mut TypeWorkBudget|
                 -> Result<Box<[usize]>, ImageFailure> {
                    let end = records
                        .start
                        .checked_add(records.len)
                        .ok_or(ImageFailure::InvalidRecord)?;
                    if records.start != child_cursor || end > child_end_u32 {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    let mut roots = Vec::new();
                    for record in records.get(&self.image.provenance_children)? {
                        push(&mut roots, root(*record)?, work)?;
                    }
                    child_cursor = end;
                    Ok(roots.into_boxed_slice())
                };
                let record = match *record {
                    ProvenanceRecord::Resource {
                        span,
                        resource,
                        arguments,
                    } => P::Resource {
                        span: self.span(span)?,
                        resource: self.resource_identity(resource)?,
                        arguments: roots(arguments, self.work)?,
                    },
                    ProvenanceRecord::Fact(span) => P::Fact(self.span(span)?),
                    ProvenanceRecord::Tuple { span, elements } => P::Tuple {
                        span: self.span(span)?,
                        elements: roots(elements, self.work)?,
                    },
                    ProvenanceRecord::Row { span, arguments } => P::Row {
                        span: self.span(span)?,
                        argument_roots: roots(arguments, self.work)?,
                    },
                    ProvenanceRecord::Function {
                        span,
                        domain,
                        codomain,
                        effect_arguments,
                    } => P::Function {
                        span: self.span(span)?,
                        domain: root(domain)?,
                        codomain: root(codomain)?,
                        effect_arguments: roots(effect_arguments, self.work)?,
                    },
                    ProvenanceRecord::Application {
                        span,
                        function,
                        argument,
                        argument_span,
                    } => P::Application {
                        span: self.span(span)?,
                        function: root(function)?,
                        argument: root(argument)?,
                        argument_span: self.span(argument_span)?,
                    },
                };
                arena.push(record);
            }
            if child_cursor != child_end_u32 {
                return Err(ImageFailure::InvalidRecord);
            }
            views.push(crate::resolved::ResolvedTypeProvenance::new(arena, root));
        }
        if next_node != self.image.provenance.len()
            || next_child != self.image.provenance_children.len()
        {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(if views.is_empty() {
            None
        } else {
            Some(RestoredProvenance { views })
        })
    }

    fn restore_prepared_record(
        &mut self,
        record: PreparedLibraryRecord,
    ) -> Result<crate::foreign::source_contract::PreparedForeignLibrary, ImageFailure> {
        let module = *get(&self.modules, record.module)?;
        let name = self.text(record.name)?;
        let origin = Origin::Source(self.span(record.span)?);
        let mut symbols = Vec::new();
        for symbol in record.symbols.get(&self.image.prepared_symbols)? {
            charge(self.work, 1)?;
            let name = self.text(symbol.name)?;
            let native_name = self.text(symbol.native_name)?;
            let origin = Origin::Source(self.span(symbol.span)?);
            push(
                &mut symbols,
                crate::foreign::source_contract::PreparedForeignSymbol {
                    member_index: usize::try_from(symbol.member_index)
                        .map_err(|_| ImageFailure::InvalidRecord)?,
                    name,
                    native_name,
                    origin,
                },
                self.work,
            )?;
        }
        Ok(crate::foreign::source_contract::PreparedForeignLibrary {
            module,
            name,
            public: record.public,
            symbols,
            origin,
        })
    }
    fn extended_registry(&mut self) -> Result<RestoredNativeRegistry, ImageFailure> {
        use crate::foreign::checked_source::*;

        let mut registry = self.registry()?;
        let mut nominal_owners = HashMap::new();
        let mut parameter_ids = HashMap::new();
        charge(
            self.work,
            self.image
                .nominal_parameters
                .len()
                .checked_add(
                    self.fact_table(&self.image.parameters, |p| p.parameters)?
                        .len(),
                )
                .ok_or(ImageFailure::Resource)?,
        )?;
        nominal_owners
            .try_reserve(self.image.nominal_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        parameter_ids
            .try_reserve(
                self.fact_table(&self.image.parameters, |p| p.parameters)?
                    .len(),
            )
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.nominal_parameters {
            charge(self.work, 1)?;
            let owner = self.nominal(record.owner)?;
            if nominal_owners.insert(owner, ()).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
            for parameter in record
                .parameters
                .get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?
            {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if id.module() != Some(owner.module()) || parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for record in &self.image.effects {
            let owner = self.effect_identity(record.id)?;
            for parameter in record
                .parameters
                .get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?
            {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if id.module() != Some(owner.module()) || parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for record in &self.image.global_parameters {
            charge(self.work, 1)?;
            let owner = self.binder_id(record.owner)?;
            let Some(module) = owner.module() else {
                return Err(ImageFailure::InvalidRecord);
            };
            if !matches!(record.owner, BinderIdentity::Resolved { .. })
                || record.parameters.len == 0
            {
                return Err(ImageFailure::InvalidRecord);
            }
            for parameter in record
                .parameters
                .get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?
            {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if id.module() != Some(module) || parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for record in &self.image.interface_owners {
            for parameter in record
                .parameters
                .get(self.fact_table(&self.image.parameters, |p| p.parameters)?)?
            {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }

        for slot in &self.image.scope_parameters {
            charge(self.work, 1)?;
            let parameter = get(
                self.fact_table(&self.image.parameters, |p| p.parameters)?,
                *slot,
            )?;
            let id = self.type_variable(parameter.id)?;
            if id.module().is_none() || parameter_ids.insert(id, ()).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }

        charge(self.work, 1)?;
        if parameter_ids.len()
            != self
                .fact_table(&self.image.parameters, |p| p.parameters)?
                .len()
        {
            return Err(ImageFailure::InvalidRecord);
        }
        drop(parameter_ids);
        drop(nominal_owners);
        let mut nominal_parameters = NominalParameterBuffer(Vec::new());
        charge(self.work, self.image.nominal_parameters.len())?;
        nominal_parameters
            .0
            .try_reserve_exact(self.image.nominal_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.nominal_parameters {
            let owner = self.nominal(record.owner)?;
            let parameters = self.parameters(record.parameters)?;
            nominal_parameters.0.push((owner, parameters.into_vec()));
        }
        registry = registry
            .with_type_parameters_with_budget(nominal_parameters.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let arena = self.provenance_arena()?;
        let mut effects = ResolvedEffectBuffer(Vec::new());
        let mut canonical_parameters = ParameterBuffer(Vec::new());
        charge(self.work, self.image.effects.len())?;
        effects
            .0
            .try_reserve_exact(self.image.effects.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.effects {
            let mirror = self.parameters(record.parameters)?;
            charge(self.work, mirror.0.len())?;
            canonical_parameters
                .0
                .try_reserve(mirror.0.len())
                .map_err(|_| ImageFailure::Resource)?;
            canonical_parameters.0.extend(mirror.into_vec());
            let effect = self.effect_data(*record, arena.as_ref())?;
            effects.0.push(effect);
        }
        registry = registry
            .with_effects_with_budget(effects.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut abstracts = Vec::new();
        for record in &self.image.abstract_nominals {
            let value = (
                self.nominal(record.id)?,
                self.text(record.spelling)?,
                self.kind(record.kind)?,
                self.span(record.origin)?,
            );
            push(&mut abstracts, value, self.work)?;
        }
        registry = registry
            .with_image_kind_facts(canonical_parameters.into_vec(), abstracts, self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        // Interface parameters and their owner rows are ordinary canonical
        // metadata, independent of the retired source-resource policy codec.
        let mut interface_parameters = ParameterBuffer(Vec::new());
        charge(self.work, self.image.scope_parameters.len())?;
        interface_parameters
            .0
            .try_reserve_exact(self.image.scope_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        for slot in &self.image.scope_parameters {
            interface_parameters.0.push(self.parameter(*get(
                self.fact_table(&self.image.parameters, |p| p.parameters)?,
                *slot,
            )?)?);
        }

        for record in &self.image.interface_owners {
            let parameters = self.parameters(record.parameters)?;
            charge(self.work, parameters.0.len())?;
            interface_parameters
                .0
                .try_reserve(parameters.0.len())
                .map_err(|_| ImageFailure::Resource)?;
            interface_parameters.0.extend(parameters.into_vec());
        }
        registry = registry
            .with_image_source_parameters(interface_parameters.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut interfaces = Vec::new();
        for record in &self.image.interface_owners {
            let id = self.interface_identity(record.id)?;
            let parameters = self.parameters(record.parameters)?;
            push(&mut interfaces, (id, parameters.into_vec()), self.work)?;
        }
        registry = registry
            .with_image_interface_owner_definitions(interfaces, self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut globals = GlobalParameterBuffer(Vec::new());
        charge(self.work, self.image.global_parameters.len())?;
        globals
            .0
            .try_reserve_exact(self.image.global_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.global_parameters {
            let owner = self.binder_id(record.owner)?;
            let parameters = self.global_parameters(record.parameters)?;
            globals.0.push((owner, parameters.into_vec()));
        }
        registry = registry
            .with_image_global_parameters(globals.into_vec(), self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut prepared = Vec::new();
        for record in &self.image.prepared_libraries {
            let library = self.restore_prepared_record(*record)?;
            charge(self.work, 1)?;
            push(&mut prepared, Arc::new(library), self.work)?;
        }
        let mut symbols = Vec::new();
        let mut libraries = HashMap::new();
        let mut library_allocations = HashMap::new();
        let mut used_libraries = vec![false; prepared.len()];
        for record in &self.image.native_symbols {
            charge(self.work, 4)?;
            let library = get(&prepared, record.prepared_library)?;
            let identity = NativeLibraryId::new(library.module(), record.library_ordinal);
            libraries
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            library_allocations
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            if libraries
                .insert(identity, record.prepared_library)
                .is_some_and(|old| old != record.prepared_library)
                || library_allocations
                    .insert(record.prepared_library, identity)
                    .is_some_and(|old| old != identity)
            {
                return Err(ImageFailure::InvalidRecord);
            }
            let operation = self.operation_identity(record.operation)?;
            let effect = registry
                .effect(operation.owner())
                .ok_or(ImageFailure::InvalidRecord)?;
            let symbol = bind_foreign_symbol(
                identity,
                Arc::clone(library),
                usize::try_from(record.symbol_index).map_err(|_| ImageFailure::InvalidRecord)?,
                effect,
                &ForeignBindingContext::new(&registry),
                self.work,
            )
            .map_err(|_| ImageFailure::RegistryAdmission)?;
            if symbol.operation() != operation {
                return Err(ImageFailure::InvalidRecord);
            }
            used_libraries[usize::try_from(record.prepared_library)
                .map_err(|_| ImageFailure::InvalidRecord)?] = true;
            push(&mut symbols, Arc::new(symbol), self.work)?;
        }
        if used_libraries.iter().any(|used| !used) {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut tagged = vec![false; symbols.len()];
        for record in &self.image.effects {
            charge(self.work, 1)?;
            if let Some(slot) = record.native_symbol {
                let symbol = get(&symbols, slot)?;
                if symbol.effect() != self.effect_identity(record.id)? {
                    return Err(ImageFailure::InvalidRecord);
                }
                let tag = tagged
                    .get_mut(usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?)
                    .ok_or(ImageFailure::InvalidRecord)?;
                if std::mem::replace(tag, true) {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        if tagged.iter().any(|used| !used) {
            return Err(ImageFailure::InvalidRecord);
        }
        for symbol in &symbols {
            registry
                .retain_native_symbol(Arc::clone(symbol), self.work)
                .map_err(|_| ImageFailure::RegistryAdmission)?;
        }
        let mut identities = Vec::new();
        for node in &self.image.nodes {
            charge(self.work, 1)?;
            if let NodeTag::CellScope { acquisition, .. } = node.tag {
                push(
                    &mut identities,
                    self.cell_acquisition(acquisition)?.identity,
                    self.work,
                )?;
            } else if let NodeTag::Region {
                identity,
                entry: false,
                ..
            } = node.tag
            {
                let identity = self.type_variable(identity)?;
                push(&mut identities, identity, self.work)?;
            }
        }
        if !registry
            .native_image_subset_with_source_scopes(&identities, &[], self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        Ok(RestoredNativeRegistry {
            registry,
            provenance: arena,
            prepared,
            symbols,
        })
    }
}

struct RestoredProvenance {
    views: Vec<crate::resolved::ResolvedTypeProvenance>,
}
impl RestoredProvenance {
    fn image_view(
        &self,
        slot: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::resolved::ResolvedTypeProvenance, ()> {
        work.charge(1)?;
        let original = self.views.get(slot).ok_or(())?;
        original.image_view(original.root(), work)
    }
}

struct RestoredNativeRegistry {
    registry: ResolvedRegistry,
    provenance: Option<RestoredProvenance>,
    prepared: Vec<Arc<crate::foreign::source_contract::PreparedForeignLibrary>>,
    symbols: Vec<Arc<crate::foreign::checked_source::CheckedForeignSymbol>>,
}

/// Holds independently validated Core and its original restored allocation
/// coordinates. These handles are needed by the generated-registration gate;
/// returning them alone never admits an executable callback.
pub(crate) struct RestoredEffectImage {
    _provenance: Option<RestoredProvenance>,
    pub(crate) program: crate::core::ValidatedEffectProgram,
    pub(crate) prepared: Vec<Arc<crate::foreign::source_contract::PreparedForeignLibrary>>,
    pub(crate) symbols: Vec<Arc<crate::foreign::checked_source::CheckedForeignSymbol>>,
    _sources: Vec<SourceFile>,
    modules: Vec<ModuleId>,
}

impl PureImage {
    pub(crate) fn restore_effect(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<RestoredEffectImage, ImageFailure> {
        charge(work, 1)?;
        if !self.effect_dialect || self.sources.is_empty() {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut decoder = Decoder {
            image: self,
            source_declaration_catalogs: HashMap::new(),

            decoded_types: HashMap::new(),
            decoded_rows: HashMap::new(),
            expected_fact_prefixes: None,
            sources: CoordinateStorage::Owned(Vec::new()),
            modules: CoordinateStorage::Owned(Vec::new()),
            work,
        };
        let mut seen_common = false;
        let mut seen_cell = false;
        let mut seen_generic_cell = false;
        let mut seen_region = false;
        let mut seen_region_facade = false;
        let mut seen_string = false;
        let mut seen_bytes = false;
        for record in &self.sources {
            charge(decoder.work, 1)?;
            let path = decoder.text(record.path)?;
            let text = decoder.text(record.text)?;
            let source = SourceFile::new_with_budget(path, text, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            let role = match record.role {
                ModuleRoleRecord::Ordinary => crate::module::ImageModuleRole::Ordinary,
                ModuleRoleRecord::BuiltinString => {
                    if std::mem::replace(&mut seen_string, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinString
                }
                ModuleRoleRecord::BuiltinBytes => {
                    if std::mem::replace(&mut seen_bytes, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinBytes
                }
                ModuleRoleRecord::BuiltinRegionFacade => {
                    if std::mem::replace(&mut seen_region_facade, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinRegionFacade
                }
                ModuleRoleRecord::BuiltinRegion => {
                    if std::mem::replace(&mut seen_region, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinRegion
                }
                ModuleRoleRecord::BuiltinGenericCell => {
                    if std::mem::replace(&mut seen_generic_cell, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinGenericCell
                }
                ModuleRoleRecord::BuiltinCell => {
                    if std::mem::replace(&mut seen_cell, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinCell
                }
                ModuleRoleRecord::BuiltinForeign => {
                    if std::mem::replace(&mut seen_common, true) {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    crate::module::ImageModuleRole::BuiltinForeign
                }
            };
            let module = crate::module::restore_image_module(&source, role, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            decoder.sources.push(source, decoder.work)?;
            decoder.modules.push(module, decoder.work)?;
        }
        let RestoredNativeRegistry {
            registry,
            provenance,
            prepared,
            symbols,
        } = decoder.extended_registry()?;
        charge(decoder.work, 1)?;
        let registry = Arc::new(registry);
        let binder_ids = decoder.source_binder_reservations()?;
        // Freeze ownership of the admitted coordinate arena outside the
        // decoder. The syntax loan borrows these exact immutable objects;
        // original registry/forest sessions remain separate per template.
        let Decoder {
            image,
            expected_fact_prefixes,
            sources,
            modules,
            source_declaration_catalogs,
            decoded_types,
            decoded_rows,
            work,
        } = decoder;
        let source_arena = sources.into_owned()?;
        let module_arena = modules.into_owned()?;
        let coordinate_loan = crate::core::validate::DeclarationCoordinateLoan::new(
            &source_arena,
            &module_arena,
            work,
        )
        .map_err(ImageFailure::Validation)?;
        let mut decoder = Decoder {
            image,
            expected_fact_prefixes,
            sources: CoordinateStorage::Borrowed(&source_arena),
            modules: CoordinateStorage::Borrowed(&module_arena),
            source_declaration_catalogs,
            decoded_types,
            decoded_rows,
            work,
        };
        let catalog = decoder.method_catalog(
            self.main_method_catalog
                .ok_or(ImageFailure::InvalidRecord)?,
        )?;
        let mut builder = crate::core::EffectCoreBuilder::with_registry_and_method_evidence(
            Arc::clone(&registry),
            Arc::clone(&catalog),
        )?;
        builder.reserve_image_reconstruction_storage(
            self.nodes.len(),
            self.binders.len(),
            decoder.work,
        )?;
        builder.reserve_image_binders(&binder_ids, decoder.work)?;
        let mut nodes = Vec::new();
        charge(decoder.work, self.nodes.len())?;
        nodes
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.nodes {
            charge(decoder.work, 1)?;
            let ty = decoder.ty(record.ty)?;
            let origin = decoder.origin(record.origin)?;
            let effects = decoder.row(record.effects.ok_or(ImageFailure::InvalidRecord)?)?;
            let node = decoder.effect_node(
                &mut builder,
                &registry,
                &nodes,
                &symbols,
                record.tag,
                ty,
                effects,
                origin,
            )?;
            nodes.push(node);
        }
        decoder.source_method_anchors(
            &mut builder,
            &nodes,
            &catalog,
            self.source_method_anchors
                .ok_or(ImageFailure::InvalidRecord)?,
        )?;
        let unchecked = builder.finish_image(*get(&nodes, self.root)?, decoder.work)?;
        let mut sources = Vec::new();
        let mut module_sources = Vec::new();
        for (module, source) in decoder.modules.iter().zip(decoder.sources.iter()) {
            push(&mut sources, source, decoder.work)?;
            push(&mut module_sources, (*module, source.id()), decoder.work)?;
        }
        let program = crate::core::validate::validate_effect_modules_with_work(
            unchecked,
            &sources,
            &module_sources,
            decoder.work,
        )
        .map_err(ImageFailure::Validation)?;
        charge(decoder.work, 1)?;
        if !program
            .node(program.root())
            .ok_or(ImageFailure::InvalidRecord)?
            .effects()
            .is_empty()
        {
            return Err(ImageFailure::InvalidRecord);
        }
        // Validation source views end here. Transfer the already admitted flat
        // coordinate arena into its private registration owner without copying.
        drop(sources);
        drop(module_sources);
        drop(decoder);
        drop(coordinate_loan);

        let sources = source_arena;
        let modules = module_arena;
        Ok(RestoredEffectImage {
            _provenance: provenance,
            program,
            prepared,
            symbols,
            _sources: sources,
            modules,
        })
    }
}

impl Decoder<'_> {
    fn cell_acquisition(
        &mut self,
        record: CellAcquisitionRecord,
    ) -> Result<crate::resolved::ResourceAcquisition, ImageFailure> {
        let builtin = *get(&self.modules, record.module)?;
        if !builtin.is_builtin_resource() {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(crate::resolved::ResourceAcquisition {
            builtin,
            identity: self.type_variable(record.identity)?,
            handle: self.binder_id(record.handle)?,
            provider: crate::interface::LexicalEvidenceId::new(
                *get(&self.modules, record.provider_module)?,
                record.provider_local,
            ),
            methods: crate::resolved::ResourceMethods::Cell([
                self.binder_id(record.read)?,
                self.binder_id(record.write)?,
            ]),
            span: self.span(record.span)?,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn effect_node(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        _registry: &ResolvedRegistry,
        nodes: &[NodeId],
        symbols: &[Arc<crate::foreign::checked_source::CheckedForeignSymbol>],
        tag: NodeTag,
        ty: IterativeTypeOwner,
        effects: crate::types::EffectRow,
        origin: OriginOwner,
    ) -> Result<NodeId, ImageFailure> {
        let node = match tag {
            NodeTag::Region {
                entry,
                api,
                identity,
                access,
                preceding,
                provider,
                body,
            } => {
                let api = *get(&self.modules, api)?;
                if !api.is_builtin_region() {
                    return Err(ImageFailure::InvalidRecord);
                }
                let identity = self.type_variable(identity)?;
                let access = self.binder(builder, access)?;
                let scope = crate::core::region::RegionScopeNode {
                    entry,
                    api,
                    identity,
                    access,
                    preceding: *get(nodes, preceding)?,
                    provider: *get(nodes, provider)?,
                    body: *get(nodes, body)?,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.region_operation(
                            crate::core::EffectOperation::Region(Box::new(scope)),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::RegionBuffer {
                api,
                context,
                operand,
                right,
                source,
                module,
                operation,
                bytes,
            } => {
                use crate::core::{
                    packed::{Intrinsic, IntrinsicNode},
                    region::{RegionBufferNode, RegionBufferOperation},
                };
                let operation = match (source, module, operation) {
                    (3, None, negative @ 0..=1) => {
                        let bytes = bytes.get(self.fact_table(&self.image.bytes, |p| p.bytes)?)?;
                        charge(self.work, bytes.len())?;
                        if bytes.last().is_none_or(|byte| *byte == 0) {
                            return Err(ImageFailure::InvalidRecord);
                        }
                        RegionBufferOperation::IntegerLiteral(Arc::new(
                            Integer::from_sign_magnitude(negative != 0, bytes),
                        ))
                    }
                    (4, None, operation @ 0..=1) if bytes == (Slice { start: 0, len: 0 }) => {
                        RegionBufferOperation::IntegerArithmetic(if operation == 0 {
                            crate::core::Primitive::Add
                        } else {
                            crate::core::Primitive::Multiply
                        })
                    }
                    (0, None, 0) => {
                        let bytes = bytes.get(self.fact_table(&self.image.bytes, |p| p.bytes)?)?;
                        charge(self.work, bytes.len())?;
                        let mut copy = Vec::new();
                        copy.try_reserve_exact(bytes.len())
                            .map_err(|_| ImageFailure::Resource)?;
                        copy.extend_from_slice(bytes);
                        RegionBufferOperation::StringLiteral(Arc::from(copy))
                    }
                    (source, Some(module), operation) if bytes == (Slice { start: 0, len: 0 }) => {
                        let module = *get(&self.modules, module)?;
                        let owner = |local| NominalTypeId::new(module, local);
                        let operation = match (source, operation) {
                            (1, 0) => Intrinsic::BytesEmpty,
                            (1, 1) => Intrinsic::BytesAppendByte {
                                appended: ConstructorId::new(owner(0), 0),
                                invalid: ConstructorId::new(owner(0), 1),
                            },
                            (1, 4) => Intrinsic::BytesAt {
                                found: ConstructorId::new(owner(1), 0),
                                invalid: ConstructorId::new(owner(1), 1),
                            },
                            (2, 1) => Intrinsic::StringToUtf8,
                            (2, 3) => Intrinsic::StringFromUtf8 {
                                decoded: ConstructorId::new(owner(0), 0),
                                invalid: ConstructorId::new(owner(0), 1),
                            },
                            _ => return Err(ImageFailure::InvalidRecord),
                        };
                        RegionBufferOperation::Intrinsic(IntrinsicNode::new(operation, module))
                    }
                    _ => return Err(ImageFailure::InvalidRecord),
                };
                let buffer = RegionBufferNode {
                    api: *get(&self.modules, api)?,
                    context: *get(nodes, context)?,
                    operand: operand.map(|id| get(nodes, id).copied()).transpose()?,
                    right: right.map(|id| get(nodes, id).copied()).transpose()?,
                    operation,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.region_operation(
                            crate::core::EffectOperation::RegionBuffer(buffer),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::RegionValueRequest { api, fields } => {
                let api = *get(&self.modules, api)?;
                let request = crate::core::region::RegionValueRequestNode {
                    api,
                    fields: usize::try_from(fields).map_err(|_| ImageFailure::InvalidRecord)?,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.region_operation(
                            crate::core::EffectOperation::RegionValueRequest(request),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::RegionTuple {
                constructor,
                api,
                context,
                storage,
                fields,
            } => {
                let api = *get(&self.modules, api)?;
                let mut elements = Vec::new();
                for field in fields.get(&self.image.node_children)? {
                    push(&mut elements, *get(nodes, *field)?, self.work)?;
                }
                let tuple = crate::core::region::RegionTupleNode {
                    constructor: constructor.map(|id| self.constructor(id)).transpose()?,
                    api,
                    context: *get(nodes, context)?,
                    storage: *get(nodes, storage)?,
                    fields: elements.into_boxed_slice(),
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.region_operation(
                            crate::core::EffectOperation::RegionTuple(tuple),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::RegionAllocate {
                api,
                context,
                request,
            } => {
                let api = *get(&self.modules, api)?;
                if !api.is_builtin_region() {
                    return Err(ImageFailure::InvalidRecord);
                }
                let allocation = crate::core::region::RegionAllocateNode {
                    api,
                    context: *get(nodes, context)?,
                    request: *get(nodes, request)?,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.region_operation(
                            crate::core::EffectOperation::RegionAllocate(allocation),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::CellScope {
                acquisition,
                handle,
                initializer,
                body,
            } => {
                let acquisition = self.cell_acquisition(acquisition)?;
                let handle = self.binder(builder, handle)?;
                let initializer = *get(nodes, initializer)?;
                let body = *get(nodes, body)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.resource_scope(
                            Box::new(crate::core::effect::ResourceScopeNode::new(
                                acquisition,
                                handle,
                                initializer,
                                body,
                            )),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Cleanup {
                callback,
                body,
                action,
                span,
                action_span,
            } => {
                let scope = crate::core::effect::CleanupScopeNode {
                    callback: self.binder_id(callback)?,
                    body: *get(nodes, body)?,
                    action: *get(nodes, action)?,
                    span: self.span(span)?,
                    action_span: self.span(action_span)?,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.cleanup_scope(scope, ty.into_inner(), effects, origin.take())
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Registration {
                handler,
                callback,
                body,
                span,
            } => {
                let scope = crate::core::effect::RegistrationScopeNode {
                    handler: crate::core::HandlerId::new(handler),
                    callback: self.binder_id(callback)?,
                    body: *get(nodes, body)?,
                    span: self.span(span)?,
                };
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.registration_scope(scope, ty.into_inner(), effects, origin.take())
                    })
                    .map_err(ImageFailure::from);
            }

            NodeTag::Handler(slot) => {
                let (id, body, effect, clauses) =
                    self.source_handler_parts(builder, nodes, slot)?;
                let (root, registration) = self.handler_contracts(slot)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.handler_with_contracts(
                            id,
                            body,
                            effect,
                            clauses,
                            ty.into_inner(),
                            effects,
                            origin.take(),
                            root,
                            registration,
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Resume {
                handler,
                owner,
                available,
                value,
            } => {
                let value = *get(nodes, value)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.resume(
                            crate::core::HandlerId::new(handler),
                            crate::resolved::ResumeId::new(owner),
                            if available {
                                crate::core::ResumeUse::Available
                            } else {
                                crate::core::ResumeUse::Consumed
                            },
                            value,
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Discard {
                handler,
                owner,
                available,
            } => {
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.discard(
                            crate::core::HandlerId::new(handler),
                            crate::resolved::ResumeId::new(owner),
                            if available {
                                crate::core::ResumeUse::Available
                            } else {
                                crate::core::ResumeUse::Consumed
                            },
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Request {
                effect,
                operation,
                operand,
            } => {
                let effect = self.structural(effect)?.instance()?;
                // Preserve template formals; final independent Core validation
                // rejects free/out-of-scope variables and inference recipes.
                let operation = self.operation_identity(operation)?;
                let operand = *get(nodes, operand)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.request(
                            effect,
                            operation,
                            operand,
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::NativeInterpret {
                body,
                interpretations,
            } => {
                let body = *get(nodes, body)?;
                let mut restored = Vec::new();
                for record in interpretations.get(&self.image.interpretations)? {
                    let instance = self.structural(record.effect)?.instance()?;
                    let symbol = get(symbols, record.symbol)?;
                    if instance.effect() != symbol.effect() || !instance.arguments().is_empty() {
                        return Err(ImageFailure::InvalidRecord);
                    }
                    push(
                        &mut restored,
                        crate::core::NativeInterpretation::new(instance, Arc::clone(symbol)),
                        self.work,
                    )?;
                }
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.native_interpret(
                            body,
                            restored.into_boxed_slice(),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::TypeAbstraction { parameters, body } => {
                let body = *get(nodes, body)?;
                let mut restored = Vec::new();
                for parameter in
                    parameters.get(self.fact_table(&self.image.quantifiers, |p| p.quantifiers)?)?
                {
                    let value = (
                        self.type_variable(parameter.id)?,
                        self.kind(parameter.kind)?,
                    );
                    push(&mut restored, value, self.work)?;
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.type_abstraction(restored, body, ty.into_inner(), origin.take())
                })?
            }
            NodeTag::TypeApplication {
                function,
                arguments,
                row_arguments,
            } => {
                let function = *get(nodes, function)?;
                let mut restored = TypeBuffer(Vec::new());
                let arguments = arguments
                    .get(self.fact_table(&self.image.type_children, |p| p.type_children)?)?;
                charge(self.work, arguments.len())?;
                restored
                    .0
                    .try_reserve_exact(arguments.len())
                    .map_err(|_| ImageFailure::Resource)?;
                for argument in arguments {
                    let argument = self.ty(*argument)?;
                    restored.0.push(argument.into_inner());
                }
                let mut rows = Vec::new();
                for row in row_arguments
                    .get(self.fact_table(&self.image.type_children, |p| p.type_children)?)?
                {
                    let row = self.structural(*row)?.row()?;
                    push(&mut rows, row, self.work)?;
                }
                builder.with_caller_type_work(self.work, |builder| {
                    builder.type_application_with_row_arguments(
                        function,
                        restored.into_vec(),
                        rows,
                        ty.into_inner(),
                        origin.take(),
                    )
                })?
            }
            tag => self.node(builder, nodes, tag, ty, origin)?,
        };
        // Pure feature builders infer their row; compare the recorded row using
        // the same allowance rather than silently accepting an altered image.
        if !builder
            .node_effects_match_with_budget(node, &effects, self.work)?
            .map_err(|()| ImageFailure::Resource)?
        {
            return Err(ImageFailure::InvalidRecord);
        }
        Ok(node)
    }
}

impl Decoder<'_> {
    // Shared construction path for original registry records and emitter-selected
    // expected source facts. Both remain unvalidated and use guarded payloads.
    fn effect_data(
        &mut self,
        record: EffectDeclarationRecord,
        arena: Option<&RestoredProvenance>,
    ) -> Result<crate::resolved::ResolvedEffectDeclaration, ImageFailure> {
        use crate::resolved::{
            ResolvedEffectDeclaration, ResolvedEffectOperation, ResolvedEffectOperationBuffer,
            ResolvedType,
        };
        charge(self.work, 1)?;
        let id = self.effect_identity(record.id)?;
        let spelling = self.text(record.spelling)?;
        let parameters = self.parameters(record.parameters)?;
        let origin = self.origin(record.origin)?;
        let span = self.span(record.span)?;
        let mut operations = ResolvedEffectOperationBuffer(Vec::new());
        let operation_records = record.operations.get(&self.image.operations)?;
        charge(self.work, operation_records.len())?;
        operations
            .0
            .try_reserve_exact(operation_records.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in operation_records {
            charge(self.work, 1)?;
            let id = self.operation_identity(record.id)?;
            let spelling = self.text(record.spelling)?;
            let ty = self.ty(record.annotation.ty)?;
            let provenance_root = usize::try_from(record.annotation.provenance)
                .map_err(|_| ImageFailure::InvalidRecord)?;
            let arena = arena.ok_or(ImageFailure::InvalidRecord)?;
            if provenance_root >= self.image.provenance_views.len() {
                return Err(ImageFailure::InvalidRecord);
            }
            let provenance = arena
                .image_view(provenance_root, self.work)
                .map_err(|()| ImageFailure::Resource)?;
            let annotation_origin = self.origin(record.annotation.origin)?;
            let annotation_span = self.span(record.annotation.span)?;
            let origin = self.origin(record.origin)?;
            let span = self.span(record.span)?;
            operations.0.push(ResolvedEffectOperation {
                id,
                spelling,
                annotation: ResolvedType {
                    ty: ty.into_inner(),
                    provenance,
                    origin: annotation_origin.take(),
                    span: annotation_span,
                },
                origin: origin.take(),
                span,
            });
        }
        Ok(ResolvedEffectDeclaration {
            native_contract: None,
            id,
            public: record.public,
            spelling,
            parameters: parameters.into_boxed_slice(),
            operations: operations.into_boxed_slice(),
            origin: origin.take(),
            span,
        })
    }
}

impl RestoredEffectImage {
    /// Drops startup-only coordinates/arena view after executable admission.
    /// The checked program/descriptor owners retain their original required data.
    pub(crate) fn into_program(self) -> crate::core::ValidatedEffectProgram {
        self.program
    }

    pub(crate) fn relocate_library(
        &self,
        module: u32,
        ordinal: u32,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::foreign::checked_source::NativeLibraryId, ImageFailure> {
        charge(work, 1)?;
        Ok(crate::foreign::checked_source::NativeLibraryId::new(
            *get(&self.modules, module)?,
            ordinal,
        ))
    }
    pub(crate) fn relocate_operation(
        &self,
        module: u32,
        effect: u32,
        operation: u32,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::types::OperationId, ImageFailure> {
        charge(work, 1)?;
        Ok(crate::types::OperationId::new(
            crate::types::EffectId::new(*get(&self.modules, module)?, effect),
            operation,
        ))
    }
}

impl PureImage {
    pub(crate) fn admit_expected_native_facts(
        &self,
        expected: &[u8],
        work: &mut TypeWorkBudget,
    ) -> Result<(), ImageFailure> {
        self.compare_native_expectations(expected, work)
    }
}

pub(crate) struct NativeBridgeEmission {
    pub(crate) plan: super::bridge::TargetResolvedForeignBridge,
    pub(crate) image_symbol: u32,
    pub(crate) symbol_index: u32,
    pub(crate) operation_module: u32,
    pub(crate) operation_effect: u32,
    pub(crate) operation_local: u32,
}
pub(crate) struct NativeLibraryEmission {
    pub(crate) image_library: u32,
    pub(crate) module: u32,
    pub(crate) ordinal: u32,
    pub(crate) members: Vec<usize>,
}
pub(crate) struct NativeBuildImage {
    pub(crate) image: PureImage,
    pub(crate) bridges: Vec<NativeBridgeEmission>,
    pub(crate) libraries: Vec<NativeLibraryEmission>,
}
#[derive(Debug)]
pub(crate) enum NativeImageFailure {
    Image(ImageFailure),
    Bridge(super::bridge::ForeignBridgeFailure),
}
impl From<ImageFailure> for NativeImageFailure {
    fn from(error: ImageFailure) -> Self {
        Self::Image(error)
    }
}

pub(crate) fn encode_effect_for_build(
    program: &crate::core::ValidatedEffectProgram,
    provenance: &[(ModuleId, Arc<SourceFile>)],
    target: &str,
    work: &mut TypeWorkBudget,
) -> Result<NativeBuildImage, NativeImageFailure> {
    encode_native_preparation(program, provenance, target, work)
}

fn encode_native_preparation(
    program: &crate::core::ValidatedEffectProgram,
    provenance: &[(ModuleId, Arc<SourceFile>)],
    target: &str,
    work: &mut TypeWorkBudget,
) -> Result<NativeBuildImage, NativeImageFailure> {
    let mut identities = Vec::new();
    charge(work, program.node_count())?;
    for node in program.nodes() {
        if let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Resource(
            scope,
        )) = &node.kind
        {
            if !scope.acquisition.builtin.is_builtin_resource() {
                return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata).into());
            }
            push(&mut identities, scope.acquisition.identity, work)?;
        } else if let crate::core::EffectExprKind::Operation(
            crate::core::EffectOperation::Region(scope),
        ) = &node.kind
        {
            if !scope.entry {
                push(&mut identities, scope.identity(), work)?;
            }
        }
    }
    if !program
        .registry()
        .native_image_subset_with_source_scopes(&identities, &[], work)
        .map_err(|_| ImageFailure::RegistryAdmission)?
    {
        return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata).into());
    }
    charge(work, 1)?;
    if !program
        .node(program.root())
        .ok_or(ImageFailure::InvalidRecord)?
        .effects()
        .is_empty()
    {
        return Err(ImageFailure::InvalidRecord.into());
    }
    let encoder = encode_program(
        program,
        provenance,
        work,
        true,
        |_encoder| Ok(()),
        |encoder, kind| encoder.encode_effect_node(kind),
    )?;
    // Descriptors are already encoded. Source interpretations select their
    // exact callbacks and each original owner's separately declared destructor.
    // The latter grants host destruction only; it is not another source effect
    // interpretation or permission to invoke it from a lifecycle template.
    let mut callback_symbols = Vec::new();
    for interpretation in &encoder.image.interpretations {
        push(&mut callback_symbols, interpretation.symbol, encoder.work)?;
    }
    let mut selected: Vec<Option<usize>> = Vec::new();
    charge(encoder.work, encoder.image.native_symbols.len())?;
    selected
        .try_reserve_exact(encoder.image.native_symbols.len())
        .map_err(|_| ImageFailure::Resource)?;
    selected.resize(encoder.image.native_symbols.len(), None);
    let mut library_slots: Vec<Option<usize>> = Vec::new();
    charge(encoder.work, encoder.image.prepared_libraries.len())?;
    library_slots
        .try_reserve_exact(encoder.image.prepared_libraries.len())
        .map_err(|_| ImageFailure::Resource)?;
    library_slots.resize(encoder.image.prepared_libraries.len(), None);
    let mut bridges = Vec::new();
    let mut libraries: Vec<NativeLibraryEmission> = Vec::new();
    for symbol_slot in callback_symbols {
        charge(encoder.work, 4)?;
        let slot = usize::try_from(symbol_slot).map_err(|_| ImageFailure::InvalidRecord)?;
        if selected
            .get(slot)
            .ok_or(ImageFailure::InvalidRecord)?
            .is_some()
        {
            continue;
        }
        let original = encoder
            .original_native_symbols
            .get(slot)
            .ok_or(ImageFailure::InvalidRecord)?;
        let (pointer, original_slot) = encoder
            .native_symbols
            .get(&original.operation())
            .ok_or(ImageFailure::InvalidRecord)?;
        if *pointer != Arc::as_ptr(original) || *original_slot != symbol_slot {
            return Err(ImageFailure::InvalidRecord.into());
        }
        let record = *encoder
            .image
            .native_symbols
            .get(slot)
            .ok_or(ImageFailure::InvalidRecord)?;
        charge(encoder.work, 1)?;
        let plan = super::bridge::plan_foreign_bridge_in_program(
            Arc::clone(original),
            target,
            program,
            encoder.work,
        )
        .map_err(NativeImageFailure::Bridge)?;
        let bridge = push(
            &mut bridges,
            NativeBridgeEmission {
                plan,
                image_symbol: symbol_slot,
                symbol_index: index(original.symbol_index())?,
                operation_module: record.operation.owner.module,
                operation_effect: record.operation.owner.local,
                operation_local: record.operation.local,
            },
            encoder.work,
        )?;
        selected[slot] = Some(usize::try_from(bridge).map_err(|_| ImageFailure::InvalidRecord)?);
        let library_slot =
            usize::try_from(record.prepared_library).map_err(|_| ImageFailure::InvalidRecord)?;
        let selection = library_slots
            .get_mut(library_slot)
            .ok_or(ImageFailure::InvalidRecord)?;
        let library = match *selection {
            Some(library) => library,
            None => {
                let prepared = encoder
                    .image
                    .prepared_libraries
                    .get(library_slot)
                    .ok_or(ImageFailure::InvalidRecord)?;
                let original_library_slot = encoder
                    .prepared_libraries
                    .get(&Arc::as_ptr(original.prepared()))
                    .ok_or(ImageFailure::InvalidRecord)?;
                if *original_library_slot != record.prepared_library {
                    return Err(ImageFailure::InvalidRecord.into());
                }
                let library = push(
                    &mut libraries,
                    NativeLibraryEmission {
                        image_library: record.prepared_library,
                        module: prepared.module,
                        ordinal: original.library().ordinal(),
                        members: Vec::new(),
                    },
                    encoder.work,
                )?;
                let library = usize::try_from(library).map_err(|_| ImageFailure::InvalidRecord)?;
                *selection = Some(library);
                library
            }
        };
        push(
            &mut libraries[library].members,
            usize::try_from(bridge).map_err(|_| ImageFailure::InvalidRecord)?,
            encoder.work,
        )?;
    }
    Ok(NativeBuildImage {
        image: encoder.image,
        bridges,
        libraries,
    })
}

#[cfg(test)]
#[path = "decoded_row_tests.rs"]
mod decoded_row_tests;

#[cfg(test)]
#[path = "structural_destination_tests.rs"]
mod structural_destination_tests;

#[path = "method_evidence_image.rs"]
mod method_evidence_image;
use method_evidence_image::{
    InheritedParameterRecord, InterfaceOwnerRecord, MethodCatalogRecord, MethodRecord,
    ResourceIdentity,
};

#[derive(Clone, Copy, Debug)]
pub(super) struct HandlerRecord {
    id: u32,
    body: u32,
    effect: u32,
    clauses: Slice,
    root: Option<HookRootRecord>,
    registration: Option<HookRegistrationRecord>,
}

#[derive(Clone, Copy, Debug)]
struct HookRootRecord {
    target: u32,
    span: SpanRecord,
    target_span: SpanRecord,
    operation: OperationIdentity,
    input: BinderIdentity,
    resume: u32,
}

#[derive(Clone, Copy, Debug)]
struct HookRegistrationRecord {
    target: u32,
    span: SpanRecord,
    target_span: SpanRecord,
    operation: OperationIdentity,
    callback: BinderIdentity,
    input: BinderIdentity,
    previous: BinderIdentity,
    next: BinderIdentity,
    resume: u32,
}
#[derive(Clone, Copy, Debug)]
pub(super) struct ClauseRecord {
    operation: OperationIdentity,
    resume: u32,
    arm: ArmRecord,
}

wire_struct!(HandlerRecord, id, body, effect, clauses, root, registration);
wire_struct!(
    HookRootRecord,
    target,
    span,
    target_span,
    operation,
    input,
    resume
);
wire_struct!(
    HookRegistrationRecord,
    target,
    span,
    target_span,
    operation,
    callback,
    input,
    previous,
    next,
    resume
);
wire_struct!(ClauseRecord, operation, resume, arm);

impl Encoder<'_> {
    pub(super) fn encode_handler(
        &mut self,
        handler: &crate::core::HandlerNode,
    ) -> Result<u32, ImageFailure> {
        let root = handler
            .hook_root()
            .map(|root| -> Result<_, ImageFailure> {
                Ok(HookRootRecord {
                    target: self.encode_structural(StructuralInput::Instance(&root.target))?,
                    span: self.span(root.span)?,
                    target_span: self.span(root.target_span)?,
                    operation: self.operation_identity(root.operation)?,
                    input: self.binder_id(root.input)?,
                    resume: root.resume.value(),
                })
            })
            .transpose()?;
        let registration = handler
            .hook_registration()
            .map(|registration| -> Result<_, ImageFailure> {
                Ok(HookRegistrationRecord {
                    target: self
                        .encode_structural(StructuralInput::Instance(&registration.target))?,
                    span: self.span(registration.span)?,
                    target_span: self.span(registration.target_span)?,
                    operation: self.operation_identity(registration.operation)?,
                    callback: self.binder_id(registration.callback)?,
                    input: self.binder_id(registration.input)?,
                    previous: self.binder_id(registration.previous)?,
                    next: self.binder_id(registration.next)?,
                    resume: registration.resume.value(),
                })
            })
            .transpose()?;
        let start = self.image.source_clauses.len();
        for clause in handler.clauses() {
            let record = ClauseRecord {
                operation: self.operation_identity(clause.operation())?,
                resume: clause.resume().value(),
                arm: ArmRecord {
                    pattern: self.encode_pattern(clause.pattern())?,
                    body: self.node(clause.body())?,
                    origin: self.encode_origin(clause.origin())?,
                },
            };
            push(&mut self.image.source_clauses, record, self.work)?;
        }
        let record = HandlerRecord {
            id: handler.id().value(),
            body: self.node(handler.body())?,
            effect: self.encode_structural(StructuralInput::Instance(handler.effect()))?,
            clauses: Slice::of(&self.image.source_clauses, start)?,
            root,
            registration,
        };
        push(&mut self.image.source_handlers, record, self.work)
    }
}

impl Decoder<'_> {
    pub(super) fn source_handler_parts(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        slot: u32,
    ) -> Result<
        (
            crate::core::HandlerId,
            NodeId,
            crate::types::EffectInstance,
            Vec<crate::core::EffectClause>,
        ),
        ImageFailure,
    > {
        let record = *get(&self.image.source_handlers, slot)?;
        let effect = self.structural(record.effect)?.instance()?;
        let body = *get(nodes, record.body)?;
        let mut clauses = Vec::new();
        for record in record.clauses.get(&self.image.source_clauses)? {
            let operation = self.operation_identity(record.operation)?;
            let pattern = self.pattern(builder, record.arm.pattern)?;
            let body = *get(nodes, record.arm.body)?;
            let origin = self.origin(record.arm.origin)?;
            let clause = crate::core::EffectClause::new(
                operation,
                crate::resolved::ResumeId::new(record.resume),
                crate::core::CoreMatchArm::new(pattern.take(), body, origin.take()),
            );
            push(&mut clauses, clause, self.work)?;
        }
        Ok((
            crate::core::HandlerId::new(record.id),
            body,
            effect,
            clauses,
        ))
    }
    pub(super) fn handler_contracts(
        &mut self,
        slot: u32,
    ) -> Result<
        (
            Option<crate::resolved::HookRootContract>,
            Option<Box<crate::resolved::HookRegistrationContract>>,
        ),
        ImageFailure,
    > {
        let record = *get(&self.image.source_handlers, slot)?;
        let root = record
            .root
            .map(|root| -> Result<_, ImageFailure> {
                Ok(crate::resolved::HookRootContract {
                    target: self.structural(root.target)?.instance()?,
                    span: self.span(root.span)?,
                    target_span: self.span(root.target_span)?,
                    operation: self.operation_identity(root.operation)?,
                    input: self.binder_id(root.input)?,
                    resume: crate::resolved::ResumeId::new(root.resume),
                })
            })
            .transpose()?;
        let registration = record
            .registration
            .map(|registration| -> Result<_, ImageFailure> {
                charge(self.work, 1)?;
                Ok(Box::new(crate::resolved::HookRegistrationContract {
                    target: self.structural(registration.target)?.instance()?,
                    span: self.span(registration.span)?,
                    target_span: self.span(registration.target_span)?,
                    operation: self.operation_identity(registration.operation)?,
                    callback: self.binder_id(registration.callback)?,
                    input: self.binder_id(registration.input)?,
                    previous: self.binder_id(registration.previous)?,
                    next: self.binder_id(registration.next)?,
                    resume: crate::resolved::ResumeId::new(registration.resume),
                }))
            })
            .transpose()?;
        Ok((root, registration))
    }
    pub(super) fn source_binder_reservations(
        &mut self,
    ) -> Result<Vec<crate::resolved::BinderId>, ImageFailure> {
        // Original forests and the main arena may repeat generated identities.
        // Reservation tracks names only; materialization and Core admission
        // still authenticate each arena's complete typed binder records.
        charge(self.work, self.image.binders.len())?;
        let mut seen = std::collections::HashSet::new();
        seen.try_reserve(self.image.binders.len())
            .map_err(|_| ImageFailure::Resource)?;
        let mut binders = Vec::new();
        for record in &self.image.binders {
            let id = self.binder_id(record.id)?;
            charge(self.work, 1)?;
            if seen.insert(id) {
                push(&mut binders, id, self.work)?;
            }
        }
        Ok(binders)
    }
}
