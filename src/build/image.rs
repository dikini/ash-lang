//! Matching-compiler private Core construction records.
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
    EffectOperation,
    OpenNativeInstance,
    ConstantOperand,
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
            Self::Resource => {
                formatter.write_str("Private program image work or storage admission refused")
            }
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum TypeTag {
    Resource(ResourceIdentity),
    Variable(TypeVariableIdentity),
    Application,
    Forall {
        parameters: Slice,
    },
    EffectfulFunction,
    ArgumentType,
    ArgumentRow,
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
    SourceScope(u32),
    ScalarPreflight {
        function: BinderIdentity,
        role: crate::foreign::scalar_preflight::ForeignScalarPreflightRole,
        module: u32,
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
    call_codecs: u32,
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
            call_codecs: index(image.call_codecs.len())?,
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
            || self.call_codecs > available.call_codecs
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
    effects: Vec<EffectDeclarationRecord>,
    operations: Vec<EffectOperationRecord>,
    prepared_representations: Vec<PreparedRepresentationRecord>,
    prepared_constants: Vec<PreparedConstantRecord>,
    prepared_parameters: Vec<PreparedParameterRecord>,
    prepared_owners: Vec<PreparedOwnerRecord>,
    prepared_owner_arguments: Vec<PreparedOwnerArgumentRecord>,
    prepared_operands: Vec<PreparedOperandRecord>,
    prepared_paths: Vec<u32>,
    prepared_projections: Vec<u32>,
    prepared_predicates: Vec<PreparedPredicateRecord>,
    prepared_outcomes: Vec<PreparedOutcomeRecord>,
    prepared_symbols: Vec<PreparedSymbolRecord>,
    prepared_libraries: Vec<PreparedLibraryRecord>,
    native_symbols: Vec<NativeSymbolRecord>,
    source_owners: Vec<SourceOwnerRecord>,
    interface_owners: Vec<InterfaceOwnerRecord>,
    resource_headers: Vec<ResourceHeaderRecord>,
    resource_arguments: Vec<ResourceArgumentRecord>,
    resource_effects: Vec<ResourceEffectRecord>,
    resource_provenance: Vec<u32>,
    source_parameters: Vec<u32>,
    source_arguments: Vec<u32>,
    source_handlers: Vec<HandlerRecord>,
    source_clauses: Vec<ClauseRecord>,
    template_nodes: Vec<NodeRecord>,
    source_graphs: Vec<TemplateGraphRecord>,
    source_templates: Vec<SourceTemplateRecord>,
    source_scopes: Vec<SourceScopeRecord>,
    source_node_pairs: Vec<NodePairRecord>,
    source_binder_pairs: Vec<BinderPairRecord>,
    source_fresh_types: Vec<FreshTypeRecord>,
    source_plain_pairs: Vec<PlainPairRecord>,
    source_substitutions: Vec<SourceSubstitutionRecord>,
    source_copies: Vec<SourceCopyRecord>,
    method_catalogs: Vec<MethodCatalogRecord>,
    source_methods: Vec<MethodRecord>,
    method_variables: Vec<TypeVariableIdentity>,
    inherited_parameters: Vec<InheritedParameterRecord>,
    main_method_catalog: Option<u32>,

    scalar_preflights: Vec<ScalarPreflightRecord>,
    call_codecs: Vec<CallCodecRecord>,
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

fn get<T>(records: &[T], slot: u32) -> Result<&T, ImageFailure> {
    records
        .get(usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?)
        .ok_or(ImageFailure::InvalidRecord)
}

struct Encoder<'a> {
    image: PureImage,
    structural: HashMap<(TypeTag, Box<[u32]>), u32>,
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
    call_codecs: HashMap<*const crate::foreign::checked_source::CheckedForeignCallCodec, u32>,
    source_owners: HashMap<
        NominalTypeId,
        (
            *const crate::foreign::source_owner::CheckedForeignOwner,
            u32,
        ),
    >,
    source_headers: HashMap<
        crate::types::ResourceDefinitionId,
        (*const crate::resolved::SourceResourceTypeFact, u32),
    >,
    source_templates: HashMap<
        *const crate::core::source_resource::CheckedSourceResourceTemplate,
        EncodedSourceTemplate,
    >,
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
    encode_program(program, provenance, work, false, |encoder, kind| {
        encoder.encode_node(kind)
    })
    .map(|encoder| encoder.image)
}

fn encode_program<'work, F: crate::core::dialect::CoreOperationFamily>(
    program: &crate::core::dialect::ValidatedCoreProgram<F>,
    provenance: &[(ModuleId, Arc<SourceFile>)],
    work: &'work mut TypeWorkBudget,
    effect_dialect: bool,
    mut encode_kind: impl FnMut(&mut Encoder<'_>, &F::Kind) -> Result<NodeTag, ImageFailure>,
) -> Result<Encoder<'work>, ImageFailure> {
    let registry = program.registry();
    let catalog = program.method_evidence();
    if (!effect_dialect && !catalog.methods().is_empty())
        || !catalog.lexical_owners().is_empty()
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
        image: PureImage {
            effect_dialect,
            ..PureImage::default()
        },
        structural: HashMap::new(),
        modules: HashMap::new(),
        sources: HashMap::new(),
        binders: HashMap::new(),
        remapped: Vec::new(),
        prepared_libraries: HashMap::new(),
        native_symbols: HashMap::new(),
        call_codecs: HashMap::new(),
        source_owners: HashMap::new(),
        source_headers: HashMap::new(),
        source_templates: HashMap::new(),
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
        // This first slice never converts a builtin role into ordinary authority.
        if module.is_builtin_cell()
            || module.is_builtin_native_buffer()
            || module.is_builtin_bytes()
            || module.is_builtin_string()
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
            SourceRecord {
                role: if module.is_builtin_foreign() {
                    ModuleRoleRecord::BuiltinForeign
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
    if effect_dialect || registry.scalar_preflights().next().is_some() {
        encoder.encode_extended_registry(registry)?;
    }
    if effect_dialect {
        encoder.image.main_method_catalog = Some(encoder.encode_method_catalog(catalog)?);
    }
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
    Ok(encoder)
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
                PureValue::Intrinsic(value) => {
                    use crate::core::packed::Intrinsic;
                    use crate::foreign::scalar_preflight::ForeignScalarPreflightRole as Role;
                    let (function, role) = match value.operation() {
                        Intrinsic::ForeignCheckedI64 { function } => (function, Role::I64),
                        Intrinsic::ForeignCheckedSizeT { function } => (function, Role::SizeT),
                        _ => return Err(ImageFailure::Unsupported(Unsupported::Intrinsic)),
                    };
                    NodeTag::ScalarPreflight {
                        function: self.binder_id(function)?,
                        role,
                        module: self.module(value.module())?,
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
                    let start = self.image.quantifiers.len();
                    for (id, kind) in abstraction.parameters() {
                        let id = self.type_variable(*id)?;
                        let kind = self.encode_kind(kind)?;
                        push(
                            &mut self.image.quantifiers,
                            QuantifierRecord { id, kind },
                            self.work,
                        )?;
                    }
                    NodeTag::TypeAbstraction {
                        parameters: Slice::of(&self.image.quantifiers, start)?,
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
    sources: CoordinateStorage<'a, SourceFile>,
    modules: CoordinateStorage<'a, ModuleId>,
    work: &'a mut TypeWorkBudget,
}

// A private layout marker for the matching compiler/runtime only. Neither the
// embedded byte sequence nor its numeric tags promise compatibility.
const PRIVATE_MAGIC: &[u8] = b"ash-private-program\x08";

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

#[path = "source_resource_image.rs"]
mod source_resource_image;
use source_resource_image::{
    BinderPairRecord, ClauseRecord, EncodedSourceTemplate, FreshTypeRecord, HandlerRecord,
    InheritedParameterRecord, InterfaceOwnerRecord, MethodCatalogRecord, MethodRecord,
    NodePairRecord, PlainPairRecord, ResourceArgumentRecord, ResourceEffectRecord,
    ResourceHeaderRecord, ResourceIdentity, RestoredSourceTemplate, SourceCopyRecord,
    SourceScopeRecord, SourceSubstitutionRecord, SourceTemplateRecord, TemplateGraphRecord,
};

wire_struct!(Slice, 8, start, len);
wire_struct!(
    NativeFactPrefixes,
    52,
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
    call_codecs
);
wire_struct!(SourceRecord, 17, role, path, text);
wire_struct!(SpanRecord, 12, source, start, end);
wire_struct!(NominalId, 8, module, local);
wire_struct!(ConstructorIdentity, 12, owner, local);
wire_struct!(TypeRecord, 9, tag, children);
wire_struct!(BinderRecord, 13, id, ty, origin);
wire_struct!(PatternRecord, 17, tag, children, ty, origin);
wire_struct!(ArmRecord, 12, pattern, body, origin);
wire_struct!(RecursiveMemberRecord, 8, binder, initializer);
wire_struct!(NodeRecord, 10, effects, tag, ty, origin);
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
            Self::ScalarPreflight {
                function,
                role,
                module,
            } => {
                21u8.write(writer)?;
                function.write(writer)?;
                role.write(writer)?;
                module.write(writer)
            }
            Self::SourceScope(slot) => {
                20u8.write(writer)?;
                slot.write(writer)
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
            21 => Self::ScalarPreflight {
                function: Wire::read(reader)?,
                role: Wire::read(reader)?,
                module: Wire::read(reader)?,
            },
            20 => Self::SourceScope(Wire::read(reader)?),
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
        writer.table(&self.effects)?;
        writer.table(&self.operations)?;
        writer.table(&self.prepared_representations)?;
        writer.table(&self.prepared_constants)?;
        writer.table(&self.prepared_parameters)?;
        writer.table(&self.prepared_owners)?;
        writer.table(&self.prepared_owner_arguments)?;
        writer.table(&self.prepared_operands)?;
        writer.table(&self.prepared_paths)?;
        writer.table(&self.prepared_projections)?;
        writer.table(&self.prepared_predicates)?;
        writer.table(&self.prepared_outcomes)?;
        writer.table(&self.prepared_symbols)?;
        writer.table(&self.prepared_libraries)?;
        writer.table(&self.native_symbols)?;
        writer.table(&self.source_owners)?;
        writer.table(&self.interface_owners)?;
        writer.table(&self.resource_headers)?;
        writer.table(&self.resource_arguments)?;
        writer.table(&self.resource_effects)?;
        writer.table(&self.resource_provenance)?;
        writer.table(&self.source_parameters)?;
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
        self.main_method_catalog.write(writer)?;
        writer.table(if executable {
            &self.source_arguments
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_handlers
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_clauses
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.template_nodes
        } else {
            &[]
        })?;
        writer.table(if executable { &self.source_graphs } else { &[] })?;
        writer.table(if executable {
            &self.source_templates
        } else {
            &[]
        })?;
        writer.table(if executable { &self.source_scopes } else { &[] })?;
        writer.table(if executable {
            &self.source_node_pairs
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_binder_pairs
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_fresh_types
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_plain_pairs
        } else {
            &[]
        })?;
        writer.table(if executable {
            &self.source_substitutions
        } else {
            &[]
        })?;
        writer.table(if executable { &self.source_copies } else { &[] })?;

        writer.table(&self.scalar_preflights)?;
        writer.table(native_fact_table(
            &self.call_codecs,
            prefixes.call_codecs,
            executable,
        )?)?;
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
            effects: reader.table()?,
            operations: reader.table()?,
            prepared_representations: reader.table()?,
            prepared_constants: reader.table()?,
            prepared_parameters: reader.table()?,
            prepared_owners: reader.table()?,
            prepared_owner_arguments: reader.table()?,
            prepared_operands: reader.table()?,
            prepared_paths: reader.table()?,
            prepared_projections: reader.table()?,
            prepared_predicates: reader.table()?,
            prepared_outcomes: reader.table()?,
            prepared_symbols: reader.table()?,
            prepared_libraries: reader.table()?,
            native_symbols: reader.table()?,
            source_owners: reader.table()?,
            interface_owners: reader.table()?,
            resource_headers: reader.table()?,
            resource_arguments: reader.table()?,
            resource_effects: reader.table()?,
            resource_provenance: reader.table()?,
            source_parameters: reader.table()?,
            method_catalogs: reader.table()?,
            source_methods: reader.table()?,
            method_variables: reader.table()?,
            inherited_parameters: reader.table()?,
            main_method_catalog: Wire::read(&mut reader)?,
            source_arguments: reader.table()?,
            source_handlers: reader.table()?,
            source_clauses: reader.table()?,
            template_nodes: reader.table()?,
            source_graphs: reader.table()?,
            source_templates: reader.table()?,
            source_scopes: reader.table()?,
            source_node_pairs: reader.table()?,
            source_binder_pairs: reader.table()?,
            source_fresh_types: reader.table()?,
            source_plain_pairs: reader.table()?,
            source_substitutions: reader.table()?,
            source_copies: reader.table()?,

            scalar_preflights: reader.table()?,
            call_codecs: reader.table()?,
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
        // The Pure entry stays closed to Effect metadata. Effect reconstruction
        // has a separate validated-family entry, not a silent dialect conversion.
        charge(work, 1)?;
        if self.effect_dialect
            || !self.quantifiers.is_empty()
            || !self.global_parameters.is_empty()
            || !self.abstract_nominals.is_empty()
            || !self.effects.is_empty()
            || !self.operations.is_empty()
            || !self.prepared_representations.is_empty()
            || !self.prepared_constants.is_empty()
            || !self.prepared_parameters.is_empty()
            || !self.prepared_owners.is_empty()
            || !self.prepared_owner_arguments.is_empty()
            || !self.prepared_operands.is_empty()
            || !self.prepared_paths.is_empty()
            || !self.prepared_projections.is_empty()
            || !self.prepared_predicates.is_empty()
            || !self.prepared_outcomes.is_empty()
            || !self.prepared_symbols.is_empty()
            || !self.prepared_libraries.is_empty()
            || !self.native_symbols.is_empty()
            || !self.source_owners.is_empty()
            || !self.interface_owners.is_empty()
            || !self.resource_headers.is_empty()
            || !self.resource_arguments.is_empty()
            || !self.resource_effects.is_empty()
            || !self.resource_provenance.is_empty()
            || !self.source_parameters.is_empty()
            || !self.method_catalogs.is_empty()
            || !self.source_methods.is_empty()
            || !self.method_variables.is_empty()
            || !self.inherited_parameters.is_empty()
            || self.main_method_catalog.is_some()
            || !self.source_arguments.is_empty()
            || !self.source_handlers.is_empty()
            || !self.source_clauses.is_empty()
            || !self.template_nodes.is_empty()
            || !self.source_graphs.is_empty()
            || !self.source_templates.is_empty()
            || !self.source_scopes.is_empty()
            || !self.source_node_pairs.is_empty()
            || !self.source_binder_pairs.is_empty()
            || !self.source_fresh_types.is_empty()
            || !self.source_plain_pairs.is_empty()
            || !self.source_substitutions.is_empty()
            || !self.source_copies.is_empty()
            || !self.interpretations.is_empty()
        {
            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
        }
        let mut decoder = Decoder {
            image: self,
            sources: CoordinateStorage::Owned(Vec::new()),
            modules: CoordinateStorage::Owned(Vec::new()),
            work,
        };
        if self.sources.is_empty() {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut seen_common = false;
        for record in &self.sources {
            charge(decoder.work, 1)?;
            let path = decoder.text(record.path)?;
            let text = decoder.text(record.text)?;
            let source = SourceFile::new_with_budget(path, text, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            let role = match record.role {
                ModuleRoleRecord::Ordinary => crate::module::ImageModuleRole::Ordinary,
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
            if !self.kinds.is_empty()
                || !self.parameters.is_empty()
                || !self.nominal_parameters.is_empty()
                || !self.provenance.is_empty()
                || !self.provenance_children.is_empty()
                || !self.call_codecs.is_empty()
                || !self.scalar_preflights.is_empty()
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
        builder.reserve_provider_draft_binders(&binder_ids, decoder.work)?;
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
        let unchecked = builder.finish_provider_draft(root, decoder.work)?;
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
        self.structural(root)?.ty()
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
            NodeTag::Handler(_)
            | NodeTag::Resume { .. }
            | NodeTag::Discard { .. }
            | NodeTag::SourceScope(_)
            | NodeTag::Request { .. }
            | NodeTag::NativeInterpret { .. }
            | NodeTag::TypeAbstraction { .. }
            | NodeTag::TypeApplication { .. } => {
                return Err(ImageFailure::Unsupported(Unsupported::ErasedTypeOperation));
            }
            NodeTag::ScalarPreflight {
                function,
                role,
                module,
            } => {
                use crate::core::packed::Intrinsic;
                use crate::foreign::scalar_preflight::ForeignScalarPreflightRole as Role;
                let function = self.binder_id(function)?;
                let module = *get(&self.modules, module)?;
                let operation = match role {
                    Role::I64 => Intrinsic::ForeignCheckedI64 { function },
                    Role::SizeT => Intrinsic::ForeignCheckedSizeT { function },
                };
                builder.with_caller_type_work(self.work, |builder| {
                    builder.intrinsic(operation, module, ty.into_inner(), origin.take())
                })
            }
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
        malformed_prefix[prefix_start..prefix_start + 4].copy_from_slice(&u32::MAX.to_le_bytes());
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
                modules: HashMap::from([(module, 0)]),
                sources: HashMap::new(),
                binders: HashMap::new(),
                remapped: Vec::new(),
                prepared_libraries: HashMap::new(),
                native_symbols: HashMap::new(),
                call_codecs: HashMap::new(),
                source_owners: HashMap::new(),
                source_headers: HashMap::new(),
                source_templates: HashMap::new(),
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
    fn opaque_owner_metadata_restores_shared_identity_without_owner_execution() {
        let tree = SourceTree::new();
        tree.write("entry.ash", r#"import @builtin.foreign as Foreign
foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    owner State<T, R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<Delta : EffectRow, R, T> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<T, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        operand 0 from 0 scalar
        output result as owner(State<T, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<T, Delta : EffectRow, R> : State<T, R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
    symbol Measure : Int -> Foreign.Call<Int> {
        name "ash_owner_image_size"
        abi (Size) -> Size
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Int ! {Measure}
main () = match perform Measure.call 42 {
    Foreign.Returned(value) => value
    Foreign.ConversionFailed(error) => 0
}
"#);
        let compiled = compile_path(tree.configuration())
            .expect("owner declarations and scalar entry compile");
        let (program, provenance) = compiled.effect_build_input().unwrap();
        let mut work = TypeWorkBudget::default();
        let build =
            encode_effect_for_build(program, provenance, "x86_64-unknown-linux-gnu", &mut work)
                .expect("scalar active member admits passive opaque owner facts");
        assert_eq!(build.bridges.len(), 1);
        assert_eq!(
            build.bridges[0].plan.call(),
            super::super::bridge::TargetBridgeCall::Scalar
        );
        assert_eq!(build.image.source_owners.len(), 1);
        let bytes = build.image.encode_bytes(&mut work).unwrap();
        drop(build);
        drop(compiled);
        drop(tree);
        let image = PureImage::decode_bytes(&bytes, &mut work).unwrap();
        let restored = image
            .restore_effect(&mut work)
            .expect("original owner correspondences independently restore");
        let acquire = restored
            .symbols
            .iter()
            .find(|symbol| symbol.symbol().name() == "Allocate")
            .unwrap();
        let teardown = restored
            .symbols
            .iter()
            .find(|symbol| symbol.symbol().name() == "Free")
            .unwrap();
        assert!(Arc::ptr_eq(
            acquire.owner().unwrap(),
            teardown.owner().unwrap()
        ));
        assert_eq!(acquire.symbol().native_type_projection(), &[1, 2]);
        assert_eq!(teardown.symbol().native_type_projection(), &[0, 2]);
        assert!(matches!(
            acquire.symbol().parameters()[0].kind(),
            crate::types::Kind::EffectRow
        ));
        assert!(matches!(
            teardown.symbol().parameters()[1].kind(),
            crate::types::Kind::EffectRow
        ));
        // An owner association cannot be removed or retargeted while preserving
        // executable identity; restoration rebinds every original symbol.
        let mut corrupt = PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        let record = corrupt
            .native_symbols
            .iter_mut()
            .find(|record| record.owner.is_some())
            .unwrap();
        record.owner = None;
        assert!(matches!(
            corrupt.restore_effect(&mut TypeWorkBudget::default()),
            Err(ImageFailure::InvalidRecord)
        ));
        let mut corrupt = PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        corrupt.source_owners[0].owner_index = u32::MAX;
        assert!(
            corrupt
                .restore_effect(&mut TypeWorkBudget::default())
                .is_err()
        );
    }

    #[test]
    fn scalar_preflight_image_reconstructs_authority_and_refuses_forged_records() {
        use crate::foreign::scalar_preflight::ForeignScalarPreflightRole as Role;
        let tree = SourceTree::new();
        tree.write("entry.ash", "import @builtin.foreign as Foreign\nmain : Unit -> Bool\nmain () = match Foreign.checked_i64 42 {\n    Foreign.Returned(value) => value == 42\n    Foreign.ConversionFailed(_) => false\n}\n");
        let compiled = compile_path(tree.configuration()).unwrap();
        let (program, provenance) = compiled.pure_build_input().unwrap();
        let image = encode(program, provenance, &mut TypeWorkBudget::default()).unwrap();
        assert_eq!(image.scalar_preflights.len(), 2);
        assert_eq!(image.call_codecs.len(), 1);
        assert_eq!(
            image.scalar_preflights[0].codec,
            image.scalar_preflights[1].codec
        );
        let bytes = image.encode_bytes(&mut TypeWorkBudget::default()).unwrap();
        drop(image);
        drop(compiled);
        drop(tree);
        let decode = || PureImage::decode_bytes(&bytes, &mut TypeWorkBudget::default()).unwrap();
        let restored = decode().restore(&mut TypeWorkBudget::default()).unwrap();
        assert_eq!(
            crate::eval::evaluate(&restored).unwrap().value.to_string(),
            "true"
        );
        let mutations: &[fn(&mut PureImage)] = &[
            |image| image.scalar_preflights[0].function = BinderIdentity::Generated(0),
            |image| {
                image.scalar_preflights[0].role = match image.scalar_preflights[0].role {
                    Role::I64 => Role::SizeT,
                    Role::SizeT => Role::I64,
                }
            },
            |image| image.scalar_preflights[0].annotation.provenance = u32::MAX,
            |image| image.scalar_preflights[0].annotation.ty = u32::MAX,
            |image| image.scalar_preflights[0].origin = u32::MAX,
            |image| image.scalar_preflights[0].source.end = u32::MAX,
            |image| image.scalar_preflights[0].codec = u32::MAX,
            |image| {
                image.scalar_preflights.pop();
            },
            |image| {
                image.scalar_preflights.push(image.scalar_preflights[0]);
            },
            |image| {
                image.call_codecs.push(image.call_codecs[0]);
            },
            |image| {
                let builtin = image
                    .sources
                    .iter_mut()
                    .find(|s| matches!(s.role, ModuleRoleRecord::BuiltinForeign))
                    .unwrap();
                builtin.role = ModuleRoleRecord::Ordinary;
            },
            |image| {
                let node = image
                    .nodes
                    .iter_mut()
                    .find(|n| matches!(n.tag, NodeTag::ScalarPreflight { .. }))
                    .unwrap();
                let NodeTag::ScalarPreflight { module, .. } = &mut node.tag else {
                    unreachable!()
                };
                *module = u32::MAX;
            },
            |image| {
                image.nodes[0].effects = Some(0);
            },
        ];
        for (case, mutate) in mutations.iter().enumerate() {
            let mut corrupted = decode();
            mutate(&mut corrupted);
            assert!(
                corrupted.restore(&mut TypeWorkBudget::default()).is_err(),
                "forged case {case}"
            );
        }
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

#[derive(Clone, Copy, Debug)]
enum ModuleRoleRecord {
    Ordinary,
    BuiltinForeign,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum TypeVariableIdentity {
    Resolved { module: u32, local: u32 },
    Generated(u32),
}

#[derive(Clone, Copy, Debug)]
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

#[derive(Clone, Copy, Debug)]
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
    Resource {
        span: SpanRecord,
        resource: ResourceIdentity,
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
struct ScalarRepresentationRecord {
    signed: bool,
    bits: u8,
    size_t: bool,
}

#[derive(Clone, Copy, Debug)]
struct ScalarValueRecord {
    negative: bool,
    magnitude: u64,
}

#[derive(Clone, Copy, Debug)]
enum RepresentationRecord {
    Scalar(ScalarRepresentationRecord),
    Opaque,
}

#[derive(Clone, Copy, Debug)]
struct PreparedRepresentationRecord {
    member_index: u32,
    name: Slice,
    representation: RepresentationRecord,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedConstantRecord {
    member_index: u32,
    name: Slice,
    representation: ScalarRepresentationRecord,
    value: ScalarValueRecord,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedParameterRecord {
    name: Slice,
    row: bool,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedOwnerRecord {
    member_index: u32,
    name: Slice,
    parameters: Slice,
    owned_parameter: u32,
    teardown_member: u32,
    representation_span: SpanRecord,
    owned_span: SpanRecord,
    teardown_span: SpanRecord,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedOwnerArgumentRecord {
    row: bool,
    parameter: u32,
}

#[derive(Clone, Copy, Debug)]
struct PreparedOwnerApplicationRecord {
    owner: u32,
    arguments: Slice,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
enum PreparedOwnerCallRecord {
    Acquire {
        application: PreparedOwnerApplicationRecord,
        first_nonnull: bool,
        condition_span: SpanRecord,
        outcome_spans: [SpanRecord; 2],
        readable_spans: [SpanRecord; 2],
    },
    Teardown {
        application: PreparedOwnerApplicationRecord,
        current_operand: u32,
        consumed_span: SpanRecord,
        block_span: SpanRecord,
        outcome_span: SpanRecord,
    },
}

#[derive(Clone, Copy, Debug)]
enum PreparedOperandRecordSource {
    Source(Slice),
    Constant(u32),
    Current(Slice),
}

#[derive(Clone, Copy, Debug)]
struct PreparedOperandRecord {
    representation: RepresentationRecord,
    source: PreparedOperandRecordSource,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedPredicateRecord {
    // Initial supported predicates all select Result. Encoding must explicitly
    // refuse Argument instead of flattening it to this record.
    value: ScalarValueRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedOutcomeRecord {
    predicates: Slice,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedSymbolRecord {
    member_index: u32,
    name: Slice,
    native_name: Slice,
    parameters: Slice,
    native_type_projection: Slice,
    operands: Slice,
    result: Option<RepresentationRecord>,
    outcomes: Slice,
    owner_call: Option<PreparedOwnerCallRecord>,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct PreparedLibraryRecord {
    module: u32,
    name: Slice,
    public: bool,
    representations: Slice,
    constants: Slice,
    owners: Slice,
    symbols: Slice,
    span: SpanRecord,
}

#[derive(Clone, Copy, Debug)]
struct NativeSymbolRecord {
    // Exactly one record per original CheckedForeignSymbol Arc. During encoding
    // use a charged/fallibly reserved Arc-allocation identity map; reject one
    // operation linked to a different original allocation. Libraries likewise
    // share one original PreparedForeignLibrary allocation and complete table.
    prepared_library: u32,
    library_ordinal: u32,
    symbol_index: u32,
    operation: OperationIdentity,
    codec: u32,
    owner: Option<u32>,
}

#[derive(Clone, Copy, Debug)]
struct SourceOwnerRecord {
    prepared_library: u32,
    library_ordinal: u32,
    owner_index: u32,
    nominal: NominalId,
}

#[derive(Clone, Copy, Debug)]
struct ScalarPreflightRecord {
    function: BinderIdentity,
    role: crate::foreign::scalar_preflight::ForeignScalarPreflightRole,
    source: SpanRecord,
    origin: u32,
    annotation: ResolvedTypeRecord,
    codec: u32,
}

#[derive(Clone, Copy, Debug)]
struct CallCodecRecord {
    module: u32,
    source: SpanRecord,
    call: NominalId,
    returned: ConstructorIdentity,
    conversion_failed: ConstructorIdentity,
    conversion_error: NominalId,
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

wire_struct!(EffectIdentity, 8, module, local);
wire_struct!(OperationIdentity, 12, owner, local);
wire_struct!(ParameterRecord, 21, id, spelling, kind, origin);
wire_struct!(QuantifierRecord, 9, id, kind);
wire_struct!(NominalParameterRecord, 16, owner, parameters);
wire_struct!(GlobalParameterRowRecord, 13, owner, parameters);
wire_struct!(AbstractNominalRecord, 32, id, spelling, kind, origin);
wire_struct!(ResolvedTypeRecord, 24, ty, provenance, origin, span);
wire_struct!(
    EffectDeclarationRecord,
    50,
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
    60,
    id,
    spelling,
    annotation,
    origin,
    span
);
wire_struct!(ScalarRepresentationRecord, 3, signed, bits, size_t);
wire_struct!(ScalarValueRecord, 9, negative, magnitude);
wire_struct!(
    PreparedRepresentationRecord,
    25,
    member_index,
    name,
    representation,
    span
);
wire_struct!(
    PreparedConstantRecord,
    36,
    member_index,
    name,
    representation,
    value,
    span
);
wire_struct!(PreparedParameterRecord, 21, name, row, span);
wire_struct!(
    PreparedOwnerRecord,
    76,
    member_index,
    name,
    parameters,
    owned_parameter,
    teardown_member,
    representation_span,
    owned_span,
    teardown_span,
    span
);
wire_struct!(PreparedOwnerArgumentRecord, 5, row, parameter);
wire_struct!(PreparedOwnerApplicationRecord, 24, owner, arguments, span);
wire_struct!(PreparedOperandRecord, 18, representation, source, span);
wire_struct!(PreparedPredicateRecord, 9, value);
wire_struct!(PreparedOutcomeRecord, 20, predicates, span);
wire_struct!(
    PreparedSymbolRecord,
    66,
    member_index,
    name,
    native_name,
    parameters,
    native_type_projection,
    operands,
    result,
    outcomes,
    owner_call,
    span
);
wire_struct!(
    PreparedLibraryRecord,
    57,
    module,
    name,
    public,
    representations,
    constants,
    owners,
    symbols,
    span
);
wire_struct!(
    NativeSymbolRecord,
    29,
    prepared_library,
    library_ordinal,
    symbol_index,
    operation,
    codec,
    owner
);
wire_struct!(
    SourceOwnerRecord,
    20,
    prepared_library,
    library_ordinal,
    owner_index,
    nominal
);
wire_struct!(
    CallCodecRecord,
    56,
    module,
    source,
    call,
    returned,
    conversion_failed,
    conversion_error
);
wire_struct!(
    ScalarPreflightRecord,
    50,
    function,
    role,
    source,
    origin,
    annotation,
    codec
);
wire_struct!(NativeInterpretationRecord, 8, effect, symbol);

impl Wire for crate::foreign::scalar_preflight::ForeignScalarPreflightRole {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::I64 => 0u8,
            Self::SizeT => 1,
        }
        .write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::I64),
            1 => Ok(Self::SizeT),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

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
        }
        .write(writer)
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Ordinary),
            1 => Ok(Self::BuiltinForeign),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for TypeVariableIdentity {
    const MINIMUM: usize = 5;
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

impl Wire for PreparedOperandRecordSource {
    const MINIMUM: usize = 5;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Source(path) => {
                0u8.write(writer)?;
                path.write(writer)
            }
            Self::Constant(index) => {
                1u8.write(writer)?;
                index.write(writer)
            }
            Self::Current(path) => {
                2u8.write(writer)?;
                path.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Source(Wire::read(reader)?)),
            1 => Ok(Self::Constant(Wire::read(reader)?)),
            2 => Ok(Self::Current(Wire::read(reader)?)),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for RepresentationRecord {
    const MINIMUM: usize = 1;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Scalar(value) => {
                0u8.write(writer)?;
                value.write(writer)
            }
            Self::Opaque => 1u8.write(writer),
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Scalar(Wire::read(reader)?)),
            1 => Ok(Self::Opaque),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for PreparedOwnerCallRecord {
    const MINIMUM: usize = 65;
    fn write(&self, writer: &mut WireWriter<'_>) -> Result<(), ImageFailure> {
        match self {
            Self::Acquire {
                application,
                first_nonnull,
                condition_span,
                outcome_spans,
                readable_spans,
            } => {
                0u8.write(writer)?;
                application.write(writer)?;
                first_nonnull.write(writer)?;
                condition_span.write(writer)?;
                for span in outcome_spans.iter().chain(readable_spans) {
                    span.write(writer)?;
                }
                Ok(())
            }
            Self::Teardown {
                application,
                current_operand,
                consumed_span,
                block_span,
                outcome_span,
            } => {
                1u8.write(writer)?;
                application.write(writer)?;
                current_operand.write(writer)?;
                consumed_span.write(writer)?;
                block_span.write(writer)?;
                outcome_span.write(writer)
            }
        }
    }
    fn read(reader: &mut WireReader<'_>) -> Result<Self, ImageFailure> {
        match u8::read(reader)? {
            0 => Ok(Self::Acquire {
                application: Wire::read(reader)?,
                first_nonnull: Wire::read(reader)?,
                condition_span: Wire::read(reader)?,
                outcome_spans: [Wire::read(reader)?, Wire::read(reader)?],
                readable_spans: [Wire::read(reader)?, Wire::read(reader)?],
            }),
            1 => Ok(Self::Teardown {
                application: Wire::read(reader)?,
                current_operand: Wire::read(reader)?,
                consumed_span: Wire::read(reader)?,
                block_span: Wire::read(reader)?,
                outcome_span: Wire::read(reader)?,
            }),
            _ => Err(ImageFailure::InvalidEncoding),
        }
    }
}

impl Wire for ProvenanceRecord {
    const MINIMUM: usize = 13;
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
                            let slot = push(&mut self.image.kinds, tag, self.work)?;
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
                    let slot = push(
                        &mut self.image.kinds,
                        KindRecord::Function { domain, codomain },
                        self.work,
                    )?;
                    push(&mut results, slot, self.work)?;
                }
            }
        }
        results
            .pop()
            .filter(|_| results.is_empty())
            .ok_or(ImageFailure::InvalidRecord)
    }

    // Keys contain only exact tags and canonical child slots. Hashing and
    // comparison never traverse owned Type/row trees or source allocations.
    fn intern_structural(&mut self, tag: TypeTag, children: &[u32]) -> Result<u32, ImageFailure> {
        // Quantifier slices are occurrence records, retained in original order.
        if matches!(tag, TypeTag::Forall { .. }) {
            let children = append(&mut self.image.type_children, children, self.work)?;
            return push(
                &mut self.image.types,
                TypeRecord { tag, children },
                self.work,
            );
        }
        charge(self.work, children.len())?;
        let mut retained = Vec::new();
        retained
            .try_reserve_exact(children.len())
            .map_err(|_| ImageFailure::Resource)?;
        retained.extend_from_slice(children);
        let key = (tag, retained.into_boxed_slice());
        let key_work = children
            .len()
            .checked_mul(2)
            .and_then(|count| count.checked_add(1))
            .ok_or(ImageFailure::Resource)?;
        charge(self.work, key_work)?;
        if let Some(slot) = self.structural.get(&key) {
            return Ok(*slot);
        }
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
                        && !matches!(input, StructuralInput::Type(Type::Variable(id))
                            if id.module().is_some_and(|module| module.is_builtin_foreign()))
                    {
                        return Err(ImageFailure::Unsupported(Unsupported::Type));
                    }
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let (tag, count) = match input {
                        StructuralInput::Type(ty) => match ty {
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
                            Type::Forall(parameters, _) => {
                                let start = self.image.quantifiers.len();
                                for (id, kind) in parameters.iter() {
                                    charge(self.work, 1)?;
                                    let id = self.type_variable(*id)?;
                                    let kind = self.encode_kind(kind)?;
                                    push(
                                        &mut self.image.quantifiers,
                                        QuantifierRecord { id, kind },
                                        self.work,
                                    )?;
                                }
                                (
                                    TypeTag::Forall {
                                        parameters: Slice::of(&self.image.quantifiers, start)?,
                                    },
                                    1,
                                )
                            }
                            Type::ResourceApply(id, arguments) => (
                                TypeTag::Resource(self.resource_identity(*id)?),
                                arguments.len(),
                            ),
                            Type::Inference(_) => {
                                return Err(ImageFailure::Unsupported(Unsupported::Type));
                            }
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
                            let (tail, lacks) = if let Some(tail) = row.tail() {
                                let crate::types::EffectRowVariable::Rigid(id) = tail.variable()
                                else {
                                    return Err(ImageFailure::Unsupported(Unsupported::Type));
                                };
                                (Some(self.type_variable(id)?), tail.lacks().len())
                            } else {
                                (None, 0)
                            };
                            (
                                TypeTag::Row {
                                    known: index(row.known().len())?,
                                    tail,
                                },
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
                            if let Some(tail) = row.tail() {
                                for instance in tail.lacks().iter().rev() {
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
                            for instance in row.known().iter().rev() {
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
                    match *get(&self.image.kinds, slot)? {
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
        enum Task {
            Visit(u32, usize),
            Finish(TypeTag, usize),
        }
        let mut tasks = Vec::new();
        let mut results: Vec<StructuralOwner> = Vec::new();
        push(&mut tasks, Task::Visit(root, 0), self.work)?;
        while let Some(task) = tasks.pop() {
            charge(self.work, 1)?;
            match task {
                Task::Visit(slot, depth) => {
                    if depth > crate::core::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Err(ImageFailure::Resource);
                    }
                    let record = *get(&self.image.types, slot)?;
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
                    let children = record.children.get(&self.image.type_children)?;
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
                            let mut arguments = Vec::new();
                            arguments
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            // Convert into guards first: an invalid later child
                            // cannot recursively drop a previously extracted Type.
                            for child in results.drain(start..) {
                                arguments.push(child.argument()?);
                            }
                            let mut owned = Vec::new();
                            charge(self.work, count)?;
                            owned
                                .try_reserve_exact(count)
                                .map_err(|_| ImageFailure::Resource)?;
                            for argument in arguments {
                                owned.push(argument.into_inner());
                            }
                            StructuralOwner::Instance(crate::types::EffectInstance::new_kinded(
                                id,
                                owned.into_boxed_slice(),
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
                            let tail = tail
                                .map(|id| {
                                    self.type_variable(id).map(|id| {
                                        (crate::types::EffectRowVariable::Rigid(id), lacks)
                                    })
                                })
                                .transpose()?;
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
                                    let mut guarded = Vec::new();
                                    charge(self.work, count)?;
                                    guarded
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for child in results.drain(start..) {
                                        guarded.push(child.argument()?);
                                    }
                                    let mut owned = Vec::new();
                                    charge(self.work, count)?;
                                    owned
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for child in guarded {
                                        owned.push(child.into_inner());
                                    }
                                    Type::ResourceApply(id, owned.into_boxed_slice())
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
                                    let mut guarded = Vec::new();
                                    charge(self.work, count)?;
                                    guarded
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for child in results.drain(start..) {
                                        guarded.push(child.ty()?);
                                    }
                                    let mut owned = Vec::new();
                                    charge(self.work, count)?;
                                    owned
                                        .try_reserve_exact(count)
                                        .map_err(|_| ImageFailure::Resource)?;
                                    for ty in guarded {
                                        owned.push(ty.into_inner());
                                    }
                                    Type::Tuple(owned.into_boxed_slice())
                                }
                                TypeTag::Forall { parameters } => {
                                    let body =
                                        results.pop().ok_or(ImageFailure::InvalidRecord)?.ty()?;
                                    let records = parameters.get(&self.image.quantifiers)?;
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
            .ok_or(ImageFailure::InvalidRecord)
    }
}

// Additional Encoder state:
// prepared_libraries: HashMap<*const PreparedForeignLibrary, u32>,
// native_symbols: HashMap<OperationId, (*const CheckedForeignSymbol, u32)>,
// call_codecs: HashMap<*const CheckedForeignCallCodec, u32>.
// Reserve each entry fallibly and precharge before every lookup/insert.

impl Encoder<'_> {
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

    fn scalar_representation(
        value: crate::foreign::source_contract::PreparedScalarRepresentation,
    ) -> ScalarRepresentationRecord {
        use crate::foreign::source_contract::PreparedScalarRepresentation as R;
        match value {
            R::Signed(bits) => ScalarRepresentationRecord {
                signed: true,
                bits,
                size_t: false,
            },
            R::Unsigned(bits) => ScalarRepresentationRecord {
                signed: false,
                bits,
                size_t: false,
            },
            R::SizeT => ScalarRepresentationRecord {
                signed: false,
                bits: 64,
                size_t: true,
            },
        }
    }

    fn representation(
        value: crate::foreign::source_contract::PreparedRepresentation,
    ) -> Result<RepresentationRecord, ImageFailure> {
        use crate::foreign::source_contract::{
            PreparedAddressRepresentation as A, PreparedRepresentation as R,
        };
        match value {
            R::Scalar(value) => Ok(RepresentationRecord::Scalar(Self::scalar_representation(
                value,
            ))),
            R::Address(A::Opaque) => Ok(RepresentationRecord::Opaque),
            R::Address(A::Bytes) => Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata)),
        }
    }

    fn encode_prepared_parameters(
        &mut self,
        parameters: &[crate::foreign::source_contract::PreparedForeignParameter],
    ) -> Result<Slice, ImageFailure> {
        let start = self.image.prepared_parameters.len();
        for parameter in parameters {
            charge(self.work, 1)?;
            let row = match parameter.kind() {
                crate::types::Kind::Type => false,
                crate::types::Kind::EffectRow => true,
                _ => return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata)),
            };
            let name = append(
                &mut self.image.bytes,
                parameter.name().as_bytes(),
                self.work,
            )?;
            let span = self.prepared_span(parameter.origin())?;
            push(
                &mut self.image.prepared_parameters,
                PreparedParameterRecord { name, row, span },
                self.work,
            )?;
        }
        Slice::of(&self.image.prepared_parameters, start)
    }

    fn encode_prepared_owner_application(
        &mut self,
        application: &crate::foreign::source_contract::PreparedOwnerApplication,
    ) -> Result<PreparedOwnerApplicationRecord, ImageFailure> {
        use crate::foreign::source_contract::PreparedOwnerArgument;
        let start = self.image.prepared_owner_arguments.len();
        for argument in application.arguments() {
            let (row, parameter) = match argument {
                PreparedOwnerArgument::Type(parameter) => (false, *parameter),
                PreparedOwnerArgument::EffectRow(_) => {
                    return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                }
            };
            push(
                &mut self.image.prepared_owner_arguments,
                PreparedOwnerArgumentRecord {
                    row,
                    parameter: index(parameter)?,
                },
                self.work,
            )?;
        }
        Ok(PreparedOwnerApplicationRecord {
            owner: index(application.owner())?,
            arguments: Slice::of(&self.image.prepared_owner_arguments, start)?,
            span: self.span(application.span())?,
        })
    }

    fn encode_prepared_owner_call(
        &mut self,
        call: &crate::foreign::source_contract::PreparedOwnerCall,
    ) -> Result<PreparedOwnerCallRecord, ImageFailure> {
        use crate::foreign::source_contract::PreparedOwnerCall;
        match call {
            PreparedOwnerCall::Acquire {
                application,
                first_nonnull,
                condition_span,
                outcome_spans,
                readable_spans,
                initialized_bytes,
            } => {
                if initialized_bytes.is_some() {
                    return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                }
                Ok(PreparedOwnerCallRecord::Acquire {
                    application: self.encode_prepared_owner_application(application)?,
                    first_nonnull: *first_nonnull,
                    condition_span: self.span(*condition_span)?,
                    outcome_spans: [self.span(outcome_spans[0])?, self.span(outcome_spans[1])?],
                    readable_spans: [self.span(readable_spans[0])?, self.span(readable_spans[1])?],
                })
            }
            PreparedOwnerCall::Teardown {
                application,
                current_operand,
                consumed_span,
                block_span,
                outcome_span,
            } => Ok(PreparedOwnerCallRecord::Teardown {
                application: self.encode_prepared_owner_application(application)?,
                current_operand: index(*current_operand)?,
                consumed_span: self.span(*consumed_span)?,
                block_span: self.span(*block_span)?,
                outcome_span: self.span(*outcome_span)?,
            }),
        }
    }

    fn encode_prepared_library(
        &mut self,
        original: &Arc<crate::foreign::source_contract::PreparedForeignLibrary>,
    ) -> Result<u32, ImageFailure> {
        use crate::foreign::source_contract::{
            PreparedAbiResult, PreparedNativePosition, PreparedOperandSource,
        };
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
        let start = self.image.prepared_representations.len();
        for representation in original.representations() {
            charge(self.work, 1)?;
            let name = append(
                &mut self.image.bytes,
                representation.name().as_bytes(),
                self.work,
            )?;
            let span = self.prepared_span(representation.origin())?;
            push(
                &mut self.image.prepared_representations,
                PreparedRepresentationRecord {
                    member_index: index(representation.member_index())?,
                    name,
                    representation: Self::representation(representation.representation())?,
                    span,
                },
                self.work,
            )?;
        }
        let representations = Slice::of(&self.image.prepared_representations, start)?;
        let start = self.image.prepared_constants.len();
        for constant in original.constants() {
            charge(self.work, 1)?;
            let name = append(&mut self.image.bytes, constant.name().as_bytes(), self.work)?;
            let span = self.prepared_span(constant.origin())?;
            let value = constant.value();
            push(
                &mut self.image.prepared_constants,
                PreparedConstantRecord {
                    member_index: index(constant.member_index())?,
                    name,
                    representation: Self::scalar_representation(constant.representation()),
                    value: ScalarValueRecord {
                        negative: value.negative,
                        magnitude: value.magnitude,
                    },
                    span,
                },
                self.work,
            )?;
        }
        let constants = Slice::of(&self.image.prepared_constants, start)?;
        let start = self.image.prepared_owners.len();
        for owner in original.owners() {
            charge(self.work, 1)?;
            if owner.representation()
                != crate::foreign::source_contract::PreparedAddressRepresentation::Opaque
            {
                return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
            }
            let name = append(&mut self.image.bytes, owner.name().as_bytes(), self.work)?;
            let parameters = self.encode_prepared_parameters(owner.parameters())?;
            let record = PreparedOwnerRecord {
                member_index: index(owner.member_index())?,
                name,
                parameters,
                owned_parameter: index(owner.owned_parameter())?,
                teardown_member: index(owner.teardown_member())?,
                representation_span: self.span(owner.representation_span())?,
                owned_span: self.span(owner.owned_span())?,
                teardown_span: self.span(owner.teardown_span())?,
                span: self.prepared_span(owner.origin())?,
            };
            push(&mut self.image.prepared_owners, record, self.work)?;
        }
        let owners = Slice::of(&self.image.prepared_owners, start)?;
        let start = self.image.prepared_symbols.len();
        for symbol in original.symbols() {
            charge(self.work, 1)?;
            let name = append(&mut self.image.bytes, symbol.name().as_bytes(), self.work)?;
            let native_name = append(
                &mut self.image.bytes,
                symbol.native_name().as_bytes(),
                self.work,
            )?;
            let span = self.prepared_span(symbol.origin())?;
            let parameters = self.encode_prepared_parameters(symbol.parameters())?;
            let projection_start = self.image.prepared_projections.len();
            for position in symbol.native_type_projection() {
                push(
                    &mut self.image.prepared_projections,
                    index(*position)?,
                    self.work,
                )?;
            }
            let native_type_projection =
                Slice::of(&self.image.prepared_projections, projection_start)?;
            let operand_start = self.image.prepared_operands.len();
            for operand in symbol.operands() {
                charge(self.work, 1)?;
                let source = match operand.source() {
                    PreparedOperandSource::Constant(position) => {
                        PreparedOperandRecordSource::Constant(index(*position)?)
                    }
                    PreparedOperandSource::Source(path) | PreparedOperandSource::Current(path) => {
                        let path_start = self.image.prepared_paths.len();
                        for position in path {
                            push(&mut self.image.prepared_paths, index(*position)?, self.work)?;
                        }
                        let path = Slice::of(&self.image.prepared_paths, path_start)?;
                        if matches!(operand.source(), PreparedOperandSource::Current(_)) {
                            PreparedOperandRecordSource::Current(path)
                        } else {
                            PreparedOperandRecordSource::Source(path)
                        }
                    }
                };
                let span = self.prepared_span(operand.origin())?;
                push(
                    &mut self.image.prepared_operands,
                    PreparedOperandRecord {
                        representation: Self::representation(operand.representation())?,
                        source,
                        span,
                    },
                    self.work,
                )?;
            }
            let operands = Slice::of(&self.image.prepared_operands, operand_start)?;
            let outcome_start = self.image.prepared_outcomes.len();
            for outcome in symbol.outcomes() {
                charge(self.work, 1)?;
                let predicate_start = self.image.prepared_predicates.len();
                for predicate in outcome.predicates() {
                    charge(self.work, 1)?;
                    if predicate.position != PreparedNativePosition::Result {
                        return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                    }
                    push(
                        &mut self.image.prepared_predicates,
                        PreparedPredicateRecord {
                            value: ScalarValueRecord {
                                negative: predicate.value.negative,
                                magnitude: predicate.value.magnitude,
                            },
                        },
                        self.work,
                    )?;
                }
                let predicates = Slice::of(&self.image.prepared_predicates, predicate_start)?;
                let span = self.prepared_span(outcome.origin())?;
                push(
                    &mut self.image.prepared_outcomes,
                    PreparedOutcomeRecord { predicates, span },
                    self.work,
                )?;
            }
            let outcomes = Slice::of(&self.image.prepared_outcomes, outcome_start)?;
            let result = match symbol.result() {
                PreparedAbiResult::Address(
                    crate::foreign::source_contract::PreparedAddressRepresentation::Opaque,
                ) => Some(RepresentationRecord::Opaque),
                PreparedAbiResult::Address(_) => {
                    return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                }
                PreparedAbiResult::Void => None,
                PreparedAbiResult::Scalar(representation) => Some(RepresentationRecord::Scalar(
                    Self::scalar_representation(representation),
                )),
            };
            let owner_call = symbol
                .owner_call()
                .map(|call| self.encode_prepared_owner_call(call))
                .transpose()?;
            push(
                &mut self.image.prepared_symbols,
                PreparedSymbolRecord {
                    member_index: index(symbol.member_index())?,
                    name,
                    native_name,
                    parameters,
                    native_type_projection,
                    operands,
                    result,
                    outcomes,
                    owner_call,
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
                representations,
                constants,
                owners,
                symbols,
                span,
            },
            self.work,
        )?;
        self.prepared_libraries.insert(key, slot);
        Ok(slot)
    }

    // The codec allocation is prepared once, shared by pure checks and calls.
    fn encode_call_codec(
        &mut self,
        codec: &Arc<crate::foreign::checked_source::CheckedForeignCallCodec>,
    ) -> Result<u32, ImageFailure> {
        let codec_pointer = Arc::as_ptr(codec);
        charge(self.work, 1)?;
        let codec_slot = if let Some(slot) = self.call_codecs.get(&codec_pointer) {
            *slot
        } else {
            charge(self.work, 1)?;
            self.call_codecs
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            let module = self.module(codec.module())?;
            let source = self.span(codec.source())?;
            let ids = codec.ids();
            let call = self.nominal(ids.call)?;
            let returned = self.constructor(ids.returned)?;
            let conversion_failed = self.constructor(ids.conversion_failed)?;
            let conversion_error = self.nominal(ids.conversion_error)?;
            let slot = push(
                &mut self.image.call_codecs,
                CallCodecRecord {
                    module,
                    source,
                    call,
                    returned,
                    conversion_failed,
                    conversion_error,
                },
                self.work,
            )?;
            self.call_codecs.insert(codec_pointer, slot);
            slot
        };
        Ok(codec_slot)
    }

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
        let owner = original
            .owner()
            .map(|owner| self.encode_source_owner(owner, prepared_library))
            .transpose()?;
        let codec_slot = self.encode_call_codec(original.call_codec())?;
        let operation = self.operation_identity(original.operation())?;
        let slot = push(
            &mut self.image.native_symbols,
            NativeSymbolRecord {
                prepared_library,
                library_ordinal: original.library().ordinal(),
                symbol_index: index(original.symbol_index())?,
                operation,
                codec: codec_slot,
                owner,
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

    fn encode_source_owner(
        &mut self,
        original: &Arc<crate::foreign::source_owner::CheckedForeignOwner>,
        prepared_library: u32,
    ) -> Result<u32, ImageFailure> {
        charge(self.work, 1)?;
        let nominal = original.nominal();
        let pointer = Arc::as_ptr(original);
        if let Some((retained, slot)) = self.source_owners.get(&nominal) {
            return if *retained == pointer {
                Ok(*slot)
            } else {
                Err(ImageFailure::InvalidRecord)
            };
        }
        self.source_owners
            .try_reserve(1)
            .map_err(|_| ImageFailure::Resource)?;
        let record = SourceOwnerRecord {
            prepared_library,
            library_ordinal: original.library().ordinal(),
            owner_index: index(original.owner_index())?,
            nominal: self.nominal(nominal)?,
        };
        let slot = push(&mut self.image.source_owners, record, self.work)?;
        self.source_owners.insert(nominal, (pointer, slot));
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
        index(
            start
                .checked_add(original.root())
                .ok_or(ImageFailure::Resource)?,
        )
    }

    fn encode_extended_registry(
        &mut self,
        registry: &ResolvedRegistry,
    ) -> Result<(), ImageFailure> {
        for (function, fact) in registry.scalar_preflights() {
            charge(self.work, 1)?;
            if function != fact.function() {
                return Err(ImageFailure::InvalidRecord);
            }
            let function = self.binder_id(function)?;
            let source = self.span(fact.source())?;
            let origin = self.encode_origin(fact.origin())?;
            let original = fact.annotation();
            let annotation = ResolvedTypeRecord {
                ty: self.encode_type(&original.ty)?,
                provenance: self.encode_provenance(&original.provenance)?,
                origin: self.encode_origin(&original.origin)?,
                span: self.span(original.span)?,
            };
            let codec = self.encode_call_codec(fact.call_codec())?;
            push(
                &mut self.image.scalar_preflights,
                ScalarPreflightRecord {
                    function,
                    role: fact.role(),
                    source,
                    origin,
                    annotation,
                    codec,
                },
                self.work,
            )?;
        }
        for (owner, parameters) in registry.nominal_parameter_entries() {
            charge(self.work, 1)?;
            let owner = self.nominal(owner)?;
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
        let mut source_families = HashMap::new();
        for header in registry.source_resource_facts() {
            charge(self.work, 1)?;
            source_families
                .try_reserve(1)
                .map_err(|_| ImageFailure::Resource)?;
            source_families.insert(header.family, ());
        }
        for (id, kind, origin) in registry.abstract_nominal_kind_entries() {
            charge(self.work, 1)?;
            if source_families.contains_key(&id) {
                continue;
            }
            let crate::resolved::NonMaterializedNominalKind::Ordinary(kind) = kind else {
                continue; // exact source family kinds are reconstructed from their original headers
            };
            let spelling = registry
                .image_abstract_nominal_name(id)
                .ok_or(ImageFailure::InvalidRecord)?;
            let spelling = append(&mut self.image.bytes, spelling.as_bytes(), self.work)?;
            let id = self.nominal(id)?;
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
        self.encode_source_headers(registry)?;
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
            EffectExprKind::Pure(kind) => self.encode_node(kind),
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                Ok(NodeTag::SourceScope(self.encode_source_scope(scope)?))
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
                    admit_closed_native_instance(interpretation.effect(), self.work)?;
                    // Preserve unused constant metadata, but do not admit active
                    // constant native operands before the scalar bridge supports them.
                    charge(self.work, interpretation.symbol().symbol().operands().len())?;
                    if interpretation.symbol().owner().is_some()
                        || !matches!(
                            interpretation.symbol().symbol().call(),
                            crate::foreign::source_contract::PreparedForeignCall::Scalar { .. }
                        )
                    {
                        return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                    }
                    for operand in interpretation.symbol().symbol().operands() {
                        match operand.source() {
                            crate::foreign::source_contract::PreparedOperandSource::Constant(_) => {
                                return Err(ImageFailure::Unsupported(
                                    Unsupported::ConstantOperand,
                                ));
                            }
                            crate::foreign::source_contract::PreparedOperandSource::Current(_) => {
                                return Err(ImageFailure::Unsupported(
                                    Unsupported::RegistryMetadata,
                                ));
                            }
                            crate::foreign::source_contract::PreparedOperandSource::Source(_) => {}
                        }
                        if !matches!(
                            operand.representation(),
                            crate::foreign::source_contract::PreparedRepresentation::Scalar(_)
                        ) {
                            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                        }
                    }
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
            _ => Err(ImageFailure::Unsupported(Unsupported::EffectOperation)),
        }
    }
}

fn admit_closed_native_instance(
    instance: &crate::types::EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<(), ImageFailure> {
    charge(work, instance.arguments().len())?;
    for argument in instance.arguments() {
        let open =
            crate::types::visit_argument_structure_with_budget(argument, work, |component, _| {
                Ok(matches!(
                    component,
                    crate::types::TypeStructureNode::Type(Type::Variable(_) | Type::Inference(_))
                        | crate::types::TypeStructureNode::Tail(_)
                ))
            })
            .map_err(|()| ImageFailure::Resource)?;
        if open {
            return Err(ImageFailure::Unsupported(Unsupported::OpenNativeInstance));
        }
    }
    Ok(())
}

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
            get(&self.image.origins, record.origin)?,
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
        let records = records.get(&self.image.parameters)?;
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
        let records = records.get(&self.image.parameters)?;
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

    // Restore one arena allocation. Each subsequent annotation only obtains a
    // paid view of a checked root; it never recursively copies this tree.
    fn provenance_arena(
        &mut self,
    ) -> Result<Option<crate::resolved::ResolvedTypeProvenance>, ImageFailure> {
        use crate::resolved::ResolvedTypeProvenanceNode as P;
        if self.image.provenance.is_empty() {
            return Ok(None);
        }
        charge(
            self.work,
            self.image
                .provenance
                .len()
                .checked_add(1)
                .ok_or(ImageFailure::Resource)?,
        )?;
        let mut arena = Vec::new();
        arena
            .try_reserve_exact(self.image.provenance.len())
            .map_err(|_| ImageFailure::Resource)?;
        for (slot, record) in self.image.provenance.iter().enumerate() {
            charge(self.work, 1)?;
            let root = |record: u32| -> Result<usize, ImageFailure> {
                let root = usize::try_from(record).map_err(|_| ImageFailure::InvalidRecord)?;
                if root >= slot {
                    return Err(ImageFailure::InvalidRecord);
                }
                Ok(root)
            };
            let roots =
                |records: Slice, work: &mut TypeWorkBudget| -> Result<Box<[usize]>, ImageFailure> {
                    let mut roots = Vec::new();
                    for record in records.get(&self.image.provenance_children)? {
                        push(&mut roots, root(*record)?, work)?;
                    }
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
        Ok(Some(crate::resolved::ResolvedTypeProvenance::new(arena, 0)))
    }

    fn scalar_representation(
        record: ScalarRepresentationRecord,
    ) -> Result<crate::foreign::source_contract::PreparedScalarRepresentation, ImageFailure> {
        use crate::foreign::source_contract::PreparedScalarRepresentation as R;
        Ok(match (record.size_t, record.signed, record.bits) {
            (true, false, 64) => R::SizeT,
            (false, true, bits @ (8 | 32 | 64)) => R::Signed(bits),
            (false, false, bits @ (8 | 32 | 64)) => R::Unsigned(bits),
            _ => return Err(ImageFailure::InvalidRecord),
        })
    }

    fn representation(
        record: RepresentationRecord,
    ) -> Result<crate::foreign::source_contract::PreparedRepresentation, ImageFailure> {
        use crate::foreign::source_contract::{
            PreparedAddressRepresentation as A, PreparedRepresentation as R,
        };
        Ok(match record {
            RepresentationRecord::Scalar(value) => R::Scalar(Self::scalar_representation(value)?),
            RepresentationRecord::Opaque => R::Address(A::Opaque),
        })
    }

    fn prepared_parameters(
        &mut self,
        records: Slice,
    ) -> Result<Vec<crate::foreign::source_contract::PrivatePreparedParameterParts>, ImageFailure>
    {
        use crate::foreign::source_contract::{
            PrivatePreparedParameterKind, PrivatePreparedParameterParts,
        };
        let mut parameters = Vec::new();
        for record in records.get(&self.image.prepared_parameters)? {
            let value = PrivatePreparedParameterParts {
                name: self.text(record.name)?,
                kind: if record.row {
                    PrivatePreparedParameterKind::EffectRow
                } else {
                    PrivatePreparedParameterKind::Type
                },
                span: self.span(record.span)?,
            };
            push(&mut parameters, value, self.work)?;
        }
        Ok(parameters)
    }

    fn prepared_owner_application(
        &mut self,
        record: PreparedOwnerApplicationRecord,
    ) -> Result<crate::foreign::source_contract::PreparedOwnerApplication, ImageFailure> {
        use crate::foreign::source_contract::{PreparedOwnerApplication, PreparedOwnerArgument};
        let mut arguments = Vec::new();
        for record in record.arguments.get(&self.image.prepared_owner_arguments)? {
            if record.row {
                return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
            }
            let parameter =
                usize::try_from(record.parameter).map_err(|_| ImageFailure::InvalidRecord)?;
            push(
                &mut arguments,
                PreparedOwnerArgument::Type(parameter),
                self.work,
            )?;
        }
        Ok(PreparedOwnerApplication {
            owner: usize::try_from(record.owner).map_err(|_| ImageFailure::InvalidRecord)?,
            arguments,
            span: self.span(record.span)?,
        })
    }

    fn prepared_owner_call(
        &mut self,
        record: PreparedOwnerCallRecord,
    ) -> Result<crate::foreign::source_contract::PreparedOwnerCall, ImageFailure> {
        use crate::foreign::source_contract::PreparedOwnerCall;
        Ok(match record {
            PreparedOwnerCallRecord::Acquire {
                application,
                first_nonnull,
                condition_span,
                outcome_spans,
                readable_spans,
            } => PreparedOwnerCall::Acquire {
                application: self.prepared_owner_application(application)?,
                first_nonnull,
                condition_span: self.span(condition_span)?,
                outcome_spans: [self.span(outcome_spans[0])?, self.span(outcome_spans[1])?],
                readable_spans: [self.span(readable_spans[0])?, self.span(readable_spans[1])?],
                initialized_bytes: None,
            },
            PreparedOwnerCallRecord::Teardown {
                application,
                current_operand,
                consumed_span,
                block_span,
                outcome_span,
            } => PreparedOwnerCall::Teardown {
                application: self.prepared_owner_application(application)?,
                current_operand: usize::try_from(current_operand)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                consumed_span: self.span(consumed_span)?,
                block_span: self.span(block_span)?,
                outcome_span: self.span(outcome_span)?,
            },
        })
    }

    fn prepared_parts(
        &mut self,
        record: PreparedLibraryRecord,
    ) -> Result<crate::foreign::source_contract::PrivatePreparedLibraryParts, ImageFailure> {
        use crate::foreign::source_contract::*;
        charge(self.work, 1)?;
        let module = *get(&self.modules, record.module)?;
        let name = self.text(record.name)?;
        let span = self.span(record.span)?;
        let mut representations = Vec::new();
        for record in record
            .representations
            .get(&self.image.prepared_representations)?
        {
            let value = PrivatePreparedRepresentationParts {
                member_index: usize::try_from(record.member_index)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                name: self.text(record.name)?,
                representation: Self::representation(record.representation)?,
                span: self.span(record.span)?,
            };
            push(&mut representations, value, self.work)?;
        }
        let mut constants = Vec::new();
        for record in record.constants.get(&self.image.prepared_constants)? {
            let value = PrivatePreparedConstantParts {
                member_index: usize::try_from(record.member_index)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                name: self.text(record.name)?,
                representation: Self::scalar_representation(record.representation)?,
                value: PreparedScalarValue {
                    negative: record.value.negative,
                    magnitude: record.value.magnitude,
                },
                span: self.span(record.span)?,
            };
            push(&mut constants, value, self.work)?;
        }
        let mut owners = Vec::new();
        for record in record.owners.get(&self.image.prepared_owners)? {
            let value = PrivatePreparedOwnerParts {
                member_index: usize::try_from(record.member_index)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                name: self.text(record.name)?,
                parameters: self.prepared_parameters(record.parameters)?,
                owned_parameter: usize::try_from(record.owned_parameter)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                representation: PreparedAddressRepresentation::Opaque,
                teardown_member: usize::try_from(record.teardown_member)
                    .map_err(|_| ImageFailure::InvalidRecord)?,
                representation_span: self.span(record.representation_span)?,
                owned_span: self.span(record.owned_span)?,
                teardown_span: self.span(record.teardown_span)?,
                span: self.span(record.span)?,
            };
            push(&mut owners, value, self.work)?;
        }
        let mut symbols = Vec::new();
        for record in record.symbols.get(&self.image.prepared_symbols)? {
            charge(self.work, 1)?;
            let name = self.text(record.name)?;
            let native_name = self.text(record.native_name)?;
            let span = self.span(record.span)?;
            let mut parameters = Vec::new();
            for record in record.parameters.get(&self.image.prepared_parameters)? {
                let value = PrivatePreparedParameterParts {
                    name: self.text(record.name)?,
                    kind: if record.row {
                        PrivatePreparedParameterKind::EffectRow
                    } else {
                        PrivatePreparedParameterKind::Type
                    },
                    span: self.span(record.span)?,
                };
                push(&mut parameters, value, self.work)?;
            }
            let mut native_type_projection = Vec::new();
            for position in record
                .native_type_projection
                .get(&self.image.prepared_projections)?
            {
                push(
                    &mut native_type_projection,
                    usize::try_from(*position).map_err(|_| ImageFailure::InvalidRecord)?,
                    self.work,
                )?;
            }
            let mut operands = Vec::new();
            for record in record.operands.get(&self.image.prepared_operands)? {
                let span = self.span(record.span)?;
                let representation = Self::representation(record.representation)?;
                let source = match record.source {
                    PreparedOperandRecordSource::Constant(index) => {
                        PreparedOperandSource::Constant(
                            usize::try_from(index).map_err(|_| ImageFailure::InvalidRecord)?,
                        )
                    }
                    PreparedOperandRecordSource::Source(path)
                    | PreparedOperandRecordSource::Current(path) => {
                        let mut restored = Vec::new();
                        for component in path.get(&self.image.prepared_paths)? {
                            push(
                                &mut restored,
                                usize::try_from(*component)
                                    .map_err(|_| ImageFailure::InvalidRecord)?,
                                self.work,
                            )?;
                        }
                        if matches!(record.source, PreparedOperandRecordSource::Current(_)) {
                            PreparedOperandSource::Current(restored)
                        } else {
                            PreparedOperandSource::Source(restored)
                        }
                    }
                };
                push(
                    &mut operands,
                    PrivatePreparedOperandParts {
                        representation,
                        source,
                        span,
                    },
                    self.work,
                )?;
            }
            let result = match record.result {
                Some(result) => match Self::representation(result)? {
                    PreparedRepresentation::Scalar(value) => PreparedAbiResult::Scalar(value),
                    PreparedRepresentation::Address(value) => PreparedAbiResult::Address(value),
                },
                None => PreparedAbiResult::Void,
            };
            let mut outcomes = Vec::new();
            for record in record.outcomes.get(&self.image.prepared_outcomes)? {
                let span = self.span(record.span)?;
                let mut predicates = Vec::new();
                for record in record.predicates.get(&self.image.prepared_predicates)? {
                    push(
                        &mut predicates,
                        PreparedOutcomePredicate {
                            position: PreparedNativePosition::Result,
                            value: PreparedScalarValue {
                                negative: record.value.negative,
                                magnitude: record.value.magnitude,
                            },
                        },
                        self.work,
                    )?;
                }
                push(
                    &mut outcomes,
                    PrivatePreparedOutcomeParts { predicates, span },
                    self.work,
                )?;
            }
            push(
                &mut symbols,
                PrivatePreparedSymbolParts {
                    member_index: usize::try_from(record.member_index)
                        .map_err(|_| ImageFailure::InvalidRecord)?,
                    name,
                    native_name,
                    parameters,
                    native_type_projection,
                    operands,
                    result,
                    call: match record.owner_call {
                        Some(call) => {
                            if !outcomes.is_empty() {
                                return Err(ImageFailure::InvalidRecord);
                            }
                            PrivatePreparedCall::Owner(self.prepared_owner_call(call)?)
                        }
                        None => PrivatePreparedCall::Scalar { outcomes },
                    },
                    span,
                },
                self.work,
            )?;
        }
        Ok(PrivatePreparedLibraryParts {
            module,
            name,
            public: record.public,
            representations,
            constants,
            owners,
            symbols,
            span,
        })
    }

    fn extended_registry(&mut self) -> Result<RestoredNativeRegistry, ImageFailure> {
        use crate::foreign::{checked_source::*, source_contract::*};
        use crate::resolved::ResolvedEffectBuffer;
        let mut registry = self.registry()?;
        let mut nominal_owners = HashMap::new();
        let mut parameter_ids = HashMap::new();
        charge(
            self.work,
            self.image
                .nominal_parameters
                .len()
                .checked_add(self.image.parameters.len())
                .ok_or(ImageFailure::Resource)?,
        )?;
        nominal_owners
            .try_reserve(self.image.nominal_parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        parameter_ids
            .try_reserve(self.image.parameters.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.nominal_parameters {
            charge(self.work, 1)?;
            let owner = self.nominal(record.owner)?;
            if nominal_owners.insert(owner, ()).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
            for parameter in record.parameters.get(&self.image.parameters)? {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if id.module() != Some(owner.module()) || parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for record in &self.image.effects {
            let owner = self.effect_identity(record.id)?;
            for parameter in record.parameters.get(&self.image.parameters)? {
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
            for parameter in record.parameters.get(&self.image.parameters)? {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if id.module() != Some(module) || parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for record in &self.image.interface_owners {
            for parameter in record.parameters().get(&self.image.parameters)? {
                charge(self.work, 1)?;
                let id = self.type_variable(parameter.id)?;
                if parameter_ids.insert(id, ()).is_some() {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        for slot in &self.image.source_parameters {
            let parameter = *get(&self.image.parameters, *slot)?;
            let id = self.type_variable(parameter.id)?;
            if parameter_ids.insert(id, ()).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        charge(self.work, 1)?;
        if parameter_ids.len() != self.image.parameters.len() {
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
            let parts = self.prepared_parts(*record)?;
            let library = restore_prepared_library(parts, self.work)
                .map_err(|_| ImageFailure::RegistryAdmission)?;
            charge(self.work, 1)?;
            push(&mut prepared, Arc::new(library), self.work)?;
        }
        let mut candidates = Vec::new();
        let mut owner_nominals = HashMap::new();
        charge(self.work, self.image.source_owners.len())?;
        owner_nominals
            .try_reserve(self.image.source_owners.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.source_owners {
            charge(self.work, 1)?;
            let library = get(&prepared, record.prepared_library)?;
            let owner_index =
                usize::try_from(record.owner_index).map_err(|_| ImageFailure::InvalidRecord)?;
            let nominal = self.nominal(record.nominal)?;
            if owner_nominals.insert(nominal, ()).is_some()
                || library.owners().get(owner_index).is_none()
            {
                return Err(ImageFailure::InvalidRecord);
            }
            push(
                &mut candidates,
                (Arc::clone(library), owner_index, nominal),
                self.work,
            )?;
        }
        registry = registry
            .with_image_source_owner_candidates(candidates, self.work)
            .map_err(|_| ImageFailure::RegistryAdmission)?;
        let mut owners = Vec::new();
        for record in &self.image.source_owners {
            let library = get(&prepared, record.prepared_library)?;
            let owner_index =
                usize::try_from(record.owner_index).map_err(|_| ImageFailure::InvalidRecord)?;
            let (nominal, parameters) = registry
                .source_owner_candidate(library, owner_index)
                .ok_or(ImageFailure::InvalidRecord)?;
            if nominal != self.nominal(record.nominal)? {
                return Err(ImageFailure::InvalidRecord);
            }
            let owner = crate::foreign::source_owner::bind_foreign_owner(
                NativeLibraryId::new(library.module(), record.library_ordinal),
                Arc::clone(library),
                owner_index,
                nominal,
                parameters,
                &registry,
                self.work,
            )
            .map_err(|_| ImageFailure::RegistryAdmission)?;
            charge(self.work, 1)?;
            push(&mut owners, Arc::new(owner), self.work)?;
        }
        // Contexts authenticate each original codec allocation once. All symbol
        // descriptors are built while this immutable registry borrow is live.
        let mut contexts = Vec::new();
        for record in &self.image.call_codecs {
            let module = *get(&self.modules, record.module)?;
            let source = self.span(record.source)?;
            let ids = ForeignCallCodecIds {
                call: self.nominal(record.call)?,
                returned: self.constructor(record.returned)?,
                conversion_failed: self.constructor(record.conversion_failed)?,
                conversion_error: self.nominal(record.conversion_error)?,
            };
            let context = ForeignBindingContext::new(&registry, module, source, ids, self.work)
                .and_then(|context| context.with_owners(&owners, self.work))
                .map_err(|_| ImageFailure::RegistryAdmission)?;
            push(&mut contexts, context, self.work)?;
        }
        let mut symbols = Vec::new();
        let mut used_libraries = Vec::new();
        let mut used_codecs = Vec::new();
        let mut used_owners = Vec::new();
        charge(self.work, owners.len())?;
        used_owners
            .try_reserve_exact(owners.len())
            .map_err(|_| ImageFailure::Resource)?;
        used_owners.resize(owners.len(), false);
        charge(
            self.work,
            prepared
                .len()
                .checked_add(contexts.len())
                .ok_or(ImageFailure::Resource)?,
        )?;
        used_libraries
            .try_reserve_exact(prepared.len())
            .map_err(|_| ImageFailure::Resource)?;
        used_codecs
            .try_reserve_exact(contexts.len())
            .map_err(|_| ImageFailure::Resource)?;
        used_libraries.resize(prepared.len(), false);
        used_codecs.resize(contexts.len(), false);
        let mut identities = HashMap::new();
        let mut libraries = HashMap::new();
        let mut library_allocations = HashMap::new();
        charge(
            self.work,
            self.image
                .native_symbols
                .len()
                .checked_mul(3)
                .ok_or(ImageFailure::Resource)?,
        )?;
        identities
            .try_reserve(self.image.native_symbols.len())
            .map_err(|_| ImageFailure::Resource)?;
        libraries
            .try_reserve(self.image.native_symbols.len())
            .map_err(|_| ImageFailure::Resource)?;
        library_allocations
            .try_reserve(self.image.native_symbols.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.image.native_symbols {
            charge(self.work, 4)?;
            let prepared_library = get(&prepared, record.prepared_library)?;
            let context = get(&contexts, record.codec)?;
            let operation = self.operation_identity(record.operation)?;
            let library = NativeLibraryId::new(prepared_library.module(), record.library_ordinal);
            if identities.insert(operation, ()).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
            // A library coordinate may have many symbols, but all must share
            // its one original allocation, not independently restored twins.
            if let Some(old) = libraries.insert(library, record.prepared_library)
                && old != record.prepared_library
            {
                return Err(ImageFailure::InvalidRecord);
            }
            charge(self.work, 1)?;
            if let Some(old) = library_allocations.insert(record.prepared_library, library)
                && old != library
            {
                return Err(ImageFailure::InvalidRecord);
            }
            let symbol = restore_foreign_symbol(
                library,
                Arc::clone(prepared_library),
                usize::try_from(record.symbol_index).map_err(|_| ImageFailure::InvalidRecord)?,
                operation.owner(),
                context,
                self.work,
            )
            .map_err(|_| ImageFailure::RegistryAdmission)?;
            if symbol.operation() != operation {
                return Err(ImageFailure::InvalidRecord);
            }
            match (record.owner, symbol.owner()) {
                (Some(slot), Some(owner)) if Arc::ptr_eq(get(&owners, slot)?, owner) => {
                    used_owners
                        [usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?] = true;
                }
                (None, None) => {}
                _ => return Err(ImageFailure::InvalidRecord),
            }
            used_libraries[usize::try_from(record.prepared_library)
                .map_err(|_| ImageFailure::InvalidRecord)?] = true;
            used_codecs
                [usize::try_from(record.codec).map_err(|_| ImageFailure::InvalidRecord)?] = true;
            push(&mut symbols, symbol, self.work)?;
        }
        let mut scalar_preflights = Vec::new();
        for record in &self.image.scalar_preflights {
            charge(self.work, 2)?;
            let context = get(&contexts, record.codec)?;
            let function = self.binder_id(record.function)?;
            let source = self.span(record.source)?;
            let origin = self.origin(record.origin)?;
            let ty = self.ty(record.annotation.ty)?;
            let annotation_origin = self.origin(record.annotation.origin)?;
            let span = self.span(record.annotation.span)?;
            let provenance = arena
                .as_ref()
                .ok_or(ImageFailure::InvalidRecord)?
                .image_view(
                    usize::try_from(record.annotation.provenance)
                        .map_err(|_| ImageFailure::InvalidRecord)?,
                    self.work,
                )
                .map_err(|_| ImageFailure::InvalidRecord)?;
            let annotation = crate::resolved::ResolvedType {
                ty: ty.into_inner(),
                provenance,
                origin: annotation_origin.take(),
                span,
            };
            let fact = crate::foreign::scalar_preflight::CheckedForeignScalarPreflight::from_image_records(
                function, record.role, source, origin.take(), annotation,
                Arc::clone(context.codec()), self.work,
            ).map_err(|_| ImageFailure::RegistryAdmission)?;
            used_codecs
                [usize::try_from(record.codec).map_err(|_| ImageFailure::InvalidRecord)?] = true;
            push(&mut scalar_preflights, Arc::new(fact), self.work)?;
        }
        drop(contexts);
        for fact in scalar_preflights {
            registry
                .retain_scalar_preflight(fact, self.work)
                .map_err(|_| ImageFailure::RegistryAdmission)?;
        }
        charge(
            self.work,
            self.image
                .effects
                .len()
                .checked_add(symbols.len())
                .and_then(|n| n.checked_add(used_libraries.len()))
                .and_then(|n| n.checked_add(used_codecs.len()))
                .ok_or(ImageFailure::Resource)?,
        )?;
        charge(self.work, used_owners.len())?;
        if used_libraries.iter().any(|used| !used)
            || used_codecs.iter().any(|used| !used)
            || used_owners.iter().any(|used| !used)
        {
            return Err(ImageFailure::InvalidRecord);
        }
        let mut tagged = Vec::new();
        tagged
            .try_reserve_exact(symbols.len())
            .map_err(|_| ImageFailure::Resource)?;
        tagged.resize(symbols.len(), false);
        for record in &self.image.effects {
            if let Some(slot) = record.native_symbol {
                let symbol = get(&symbols, slot)?;
                if symbol.effect() != self.effect_identity(record.id)? {
                    return Err(ImageFailure::InvalidRecord);
                }
                let tagged = tagged
                    .get_mut(usize::try_from(slot).map_err(|_| ImageFailure::InvalidRecord)?)
                    .ok_or(ImageFailure::InvalidRecord)?;
                if std::mem::replace(tagged, true) {
                    return Err(ImageFailure::InvalidRecord);
                }
            }
        }
        if tagged.iter().any(|used| !used) {
            return Err(ImageFailure::InvalidRecord);
        }
        for symbol in &symbols {
            charge(self.work, 1)?;
            registry
                .retain_native_symbol(Arc::clone(symbol), self.work)
                .map_err(|_| ImageFailure::RegistryAdmission)?;
        }
        registry = self.source_registry(registry, arena.as_ref())?;
        let mut identities = Vec::new();
        for scope in &self.image.source_scopes {
            let id = self.type_variable(scope.identity)?;
            push(&mut identities, id, self.work)?;
        }
        if !registry
            .native_image_subset_with_source_scopes(&identities, self.work)
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

struct RestoredNativeRegistry {
    registry: ResolvedRegistry,
    provenance: Option<crate::resolved::ResolvedTypeProvenance>,
    prepared: Vec<Arc<crate::foreign::source_contract::PreparedForeignLibrary>>,
    symbols: Vec<Arc<crate::foreign::checked_source::CheckedForeignSymbol>>,
}

/// Holds independently validated Core and its original restored allocation
/// coordinates. These handles are needed by the generated-registration gate;
/// returning them alone never admits an executable callback.
pub(crate) struct RestoredEffectImage {
    provenance: Option<crate::resolved::ResolvedTypeProvenance>,
    pub(crate) program: crate::core::ValidatedEffectProgram,
    pub(crate) prepared: Vec<Arc<crate::foreign::source_contract::PreparedForeignLibrary>>,
    pub(crate) symbols: Vec<Arc<crate::foreign::checked_source::CheckedForeignSymbol>>,
    sources: Vec<SourceFile>,
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
            sources: CoordinateStorage::Owned(Vec::new()),
            modules: CoordinateStorage::Owned(Vec::new()),
            work,
        };
        let mut seen_common = false;
        for record in &self.sources {
            charge(decoder.work, 1)?;
            let path = decoder.text(record.path)?;
            let text = decoder.text(record.text)?;
            let source = SourceFile::new_with_budget(path, text, decoder.work)
                .map_err(|_| ImageFailure::SourceAdmission)?;
            let role = match record.role {
                ModuleRoleRecord::Ordinary => crate::module::ImageModuleRole::Ordinary,
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
        let templates = decoder.source_templates(&registry, &symbols, &binder_ids)?;
        let catalog = decoder.method_catalog(
            self.main_method_catalog
                .ok_or(ImageFailure::InvalidRecord)?,
        )?;
        let mut builder =
            crate::core::EffectCoreBuilder::with_registry_and_method_evidence(registry, catalog)?;
        builder.reserve_image_reconstruction_storage(
            self.nodes.len(),
            self.binders.len(),
            decoder.work,
        )?;
        builder.reserve_provider_draft_binders(&binder_ids, decoder.work)?;
        let mut nodes = Vec::new();
        charge(decoder.work, self.nodes.len())?;
        nodes
            .try_reserve_exact(self.nodes.len())
            .map_err(|_| ImageFailure::Resource)?;
        for record in &self.nodes {
            charge(decoder.work, 1)?;
            let ty = decoder.ty(record.ty)?;
            let origin = decoder.origin(record.origin)?;
            let effects = decoder
                .structural(record.effects.ok_or(ImageFailure::InvalidRecord)?)?
                .row()?;
            let node = decoder.effect_node(
                &mut builder,
                &nodes,
                &symbols,
                &templates,
                record.tag,
                ty,
                effects,
                origin,
            )?;
            nodes.push(node);
        }
        let unchecked = builder.finish_provider_draft(*get(&nodes, self.root)?, decoder.work)?;
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
        let sources = decoder.sources.into_owned()?;
        let modules = decoder.modules.into_owned()?;
        Ok(RestoredEffectImage {
            provenance,
            program,
            prepared,
            symbols,
            sources,
            modules,
        })
    }
}

impl Decoder<'_> {
    #[allow(clippy::too_many_arguments)]
    fn effect_node(
        &mut self,
        builder: &mut crate::core::EffectCoreBuilder,
        nodes: &[NodeId],
        symbols: &[Arc<crate::foreign::checked_source::CheckedForeignSymbol>],
        templates: &[RestoredSourceTemplate],
        tag: NodeTag,
        ty: IterativeTypeOwner,
        effects: crate::types::EffectRow,
        origin: OriginOwner,
    ) -> Result<NodeId, ImageFailure> {
        let node = match tag {
            NodeTag::SourceScope(slot) => {
                let scope = self.source_scope(builder, nodes, symbols, templates, slot)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.source_resource_scope(
                            Box::new(scope),
                            ty.into_inner(),
                            effects,
                            origin.take(),
                        )
                    })
                    .map_err(ImageFailure::from);
            }
            NodeTag::Handler(slot) => {
                let (id, body, effect, clauses) =
                    self.source_handler_parts(builder, nodes, slot)?;
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.handler(
                            id,
                            body,
                            effect,
                            clauses,
                            ty.into_inner(),
                            effects,
                            origin.take(),
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
                let records = interpretations.get(&self.image.interpretations)?;
                charge(self.work, records.len())?;
                let mut interpretations = Vec::new();
                interpretations
                    .try_reserve_exact(records.len())
                    .map_err(|_| ImageFailure::Resource)?;
                for record in records {
                    charge(self.work, 2)?;
                    let effect = self.structural(record.effect)?.instance()?;
                    admit_closed_native_instance(&effect, self.work)?;
                    let symbol = get(symbols, record.symbol)?;
                    charge(self.work, symbol.symbol().operands().len())?;
                    if symbol.owner().is_some()
                        || !matches!(
                            symbol.symbol().call(),
                            crate::foreign::source_contract::PreparedForeignCall::Scalar { .. }
                        )
                    {
                        return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                    }
                    for operand in symbol.symbol().operands() {
                        match operand.source() {
                            crate::foreign::source_contract::PreparedOperandSource::Constant(_) => {
                                return Err(ImageFailure::Unsupported(
                                    Unsupported::ConstantOperand,
                                ));
                            }
                            crate::foreign::source_contract::PreparedOperandSource::Current(_) => {
                                return Err(ImageFailure::Unsupported(
                                    Unsupported::RegistryMetadata,
                                ));
                            }
                            crate::foreign::source_contract::PreparedOperandSource::Source(_) => {}
                        }
                        if !matches!(
                            operand.representation(),
                            crate::foreign::source_contract::PreparedRepresentation::Scalar(_)
                        ) {
                            return Err(ImageFailure::Unsupported(Unsupported::RegistryMetadata));
                        }
                    }
                    interpretations.push(crate::core::NativeInterpretation::new(
                        effect,
                        Arc::clone(symbol),
                    ));
                }
                return builder
                    .with_caller_type_work(self.work, |builder| {
                        builder.native_interpret(
                            body,
                            interpretations.into_boxed_slice(),
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
                for parameter in parameters.get(&self.image.quantifiers)? {
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
                let arguments = arguments.get(&self.image.type_children)?;
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
                for row in row_arguments.get(&self.image.type_children)? {
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
        let actual = builder.clone_node_effects_with_budget(node, self.work)?;
        if !crate::types::same_effect_rows_with_budget(&actual, &effects, self.work)
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
        arena: Option<&crate::resolved::ResolvedTypeProvenance>,
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
            if provenance_root >= self.image.provenance.len() {
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

/// Independently emitted fact payload, checked once against the construction
/// image. Flat records own no source/provenance arena; views borrow restoration's.
pub(crate) struct ExpectedNativeFacts {
    image: PureImage,
    effects_by_library: Vec<Vec<Option<u32>>>,
}
impl PureImage {
    pub(crate) fn admit_expected_native_facts(
        &self,
        expected: &[u8],
        work: &mut TypeWorkBudget,
    ) -> Result<ExpectedNativeFacts, ImageFailure> {
        self.compare_native_expectations(expected, work)?;
        // Decode ORIGINAL emitted facts; their byte-exact correspondence above
        // authenticates use of the already restored source/provenance coordinates.
        // No SourceFile or origin/provenance arena is reconstructed here.
        let image = Self::decode_bytes(expected, work)?;
        let mut effects_by_library = Vec::new();
        for library in &image.prepared_libraries {
            let count = library.symbols.get(&image.prepared_symbols)?.len();
            charge(work, count)?;
            let mut indices = Vec::new();
            indices
                .try_reserve_exact(count)
                .map_err(|_| ImageFailure::Resource)?;
            indices.resize(count, None);
            push(&mut effects_by_library, indices, work)?;
        }
        // ONE paid index pass, rather than scanning all effects per library.
        for (slot, effect) in image.effects.iter().enumerate() {
            charge(work, 3)?;
            let Some(native) = effect.native_symbol else {
                continue;
            };
            let native = get(&image.native_symbols, native)?;
            let library = usize::try_from(native.prepared_library)
                .map_err(|_| ImageFailure::InvalidRecord)?;
            let symbol =
                usize::try_from(native.symbol_index).map_err(|_| ImageFailure::InvalidRecord)?;
            let entry = effects_by_library
                .get_mut(library)
                .and_then(|slots| slots.get_mut(symbol))
                .ok_or(ImageFailure::InvalidRecord)?;
            if entry.replace(index(slot)?).is_some() {
                return Err(ImageFailure::InvalidRecord);
            }
        }
        Ok(ExpectedNativeFacts {
            image,
            effects_by_library,
        })
    }
}
impl ExpectedNativeFacts {
    pub(crate) fn library(
        &self,
        slot: u32,
        restored: &RestoredEffectImage,
        work: &mut TypeWorkBudget,
    ) -> Result<crate::foreign::checked_source::PrivateExecutableForeignLibraryParts, ImageFailure>
    {
        use crate::resolved::ResolvedEffectBuffer;
        charge(work, 1)?;
        let record = *get(&self.image.prepared_libraries, slot)?;
        let mut decoder = Decoder {
            image: &self.image,
            sources: CoordinateStorage::Borrowed(&restored.sources),
            modules: CoordinateStorage::Borrowed(&restored.modules),
            work,
        };
        let abi = decoder.prepared_parts(record)?;
        let index = get(&self.effects_by_library, slot)?;
        charge(decoder.work, index.len())?;
        let mut members = ResolvedEffectBuffer(Vec::new());
        members
            .0
            .try_reserve_exact(index.len())
            .map_err(|_| ImageFailure::Resource)?;
        for effect in index {
            let record = *get(
                &self.image.effects,
                effect.ok_or(ImageFailure::InvalidRecord)?,
            )?;
            let member = decoder.effect_data(record, restored.provenance.as_ref())?;
            members.0.push(member);
        }
        Ok(crate::foreign::checked_source::PrivateExecutableForeignLibraryParts { abi, members })
    }
}

/// Emitter coordinates selected from the ORIGINAL checked descriptor allocation.
/// These records are passive literals; startup independently relocates/checks them.
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
    let mut identities = Vec::new();
    charge(work, program.node_count())?;
    for node in program.nodes() {
        if let crate::core::EffectExprKind::Operation(
            crate::core::EffectOperation::SourceResourceScope(scope),
        ) = &node.kind
        {
            push(&mut identities, scope.identity(), work)?;
        }
    }
    if !program
        .registry()
        .native_image_subset_with_source_scopes(&identities, work)
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
    let encoder = encode_program(program, provenance, work, true, |encoder, kind| {
        encoder.encode_effect_node(kind)
    })?;
    // The image already contains every descriptor. Generate callbacks only for
    // interpreter members, each selected once from the original allocation.
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
    for interpretation in &encoder.image.interpretations {
        charge(encoder.work, 4)?;
        let slot =
            usize::try_from(interpretation.symbol).map_err(|_| ImageFailure::InvalidRecord)?;
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
        if *pointer != Arc::as_ptr(original) || *original_slot != interpretation.symbol {
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
                image_symbol: interpretation.symbol,
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
