//! Checked source contracts and retained experimental host registrations.
//!
//! Source declarations and registrations are passive. Checked source contracts
//! retain defining operation identities for generated native bridges; retained
//! DN-0036 registrations use their separate manifest/adapter execution boundary.
//!
//! SQLite libraries use passive Ash declarations and generated native bridges.
//! The product API supplies no library-specific SQLite registration:
//!
//! ```compile_fail
//! use ash::foreign::sqlite_manifest;
//! ```
mod arena;
mod checked_control;
#[cfg(test)]
pub(crate) use checked_control::assert_dependent_header_refused_before_entry;
// Historical manifest data is needed by generic registration unit tests only.
// Production SQLite interfaces come from passive Ash source declarations.
#[cfg(test)]
use crate as contract;
#[cfg(test)]
#[path = "../foreign-adapter/src/sqlite_manifest.rs"]
mod sqlite_reference;
#[cfg(test)]
pub(crate) use sqlite_reference::sqlite_manifest;
pub(crate) mod checked_builtins;
pub mod checked_source;
pub mod runtime;
pub(crate) mod scalar_preflight;
pub(crate) mod source_access;
pub mod source_contract;
pub mod source_owner;
pub mod source_runtime;
pub use arena::{arena_manifest, typed_arena_manifest};

use crate::{
    interface::{InterfaceId, MethodId},
    module::{ForeignModuleAdmission, ForeignOperationRole, ForeignRegistrationId},
    resolved::{
        ResolvedEffectDeclaration, ResolvedInterfaceDeclaration, ResolvedNominalDeclarationKind,
        ResolvedNominalType, ResolvedRegistry, ResolvedTypeVariable,
    },
    source::{Origin, Span},
    types::{ConstructorId, EffectId, Kind, NominalTypeId, OperationId, Type, TypeVariableId},
};
use std::{
    collections::{BTreeMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

/// Authored foreign categories. Coordinates are untrusted until binding checks
/// the complete original declarations and canonical schemes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForeignTypeCategory {
    /// Ordinary constructor data, copied through the existing codec.
    Data,
    /// Opaque state owned by a resource scope.
    State,
    /// Independent immutable layout metadata for one payload parameter.
    LayoutWitness {
        /// Position of the represented payload type.
        payload_parameter: usize,
    },
    /// Nonowning object access, distinct from resource state and copied data.
    Reference {
        /// Position of the live storage owner identity.
        owner_parameter: usize,
        /// Position of the stored payload type.
        payload_parameter: usize,
    },
}
impl ForeignTypeCategory {
    const fn is_opaque(self) -> bool {
        !matches!(self, Self::Data)
    }
    const fn is_foundation(self) -> bool {
        matches!(self, Self::LayoutWitness { .. } | Self::Reference { .. })
    }
}

/// One foreign family with category-specific parameter roles.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignTypeDeclaration {
    /// Defining nominal spelling.
    pub name: String,
    /// Ordered kind-Type parameters.
    pub parameters: Vec<String>,
    /// Constructor/state/witness/reference category and its parameter roles.
    pub category: ForeignTypeCategory,
    /// Ordinary constructors, in codec field order. Opaque categories require none.
    pub constructors: Vec<ForeignConstructorDeclaration>,
}
/// A constructor and its optional ordinary Ash payload type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignConstructorDeclaration {
    /// Defining constructor spelling.
    pub name: String,
    /// Current Ash value type syntax; parsed by the existing frontend.
    pub payload: Option<String>,
}
/// One parameterized native effect.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignEffectDeclaration {
    /// Defining effect spelling.
    pub name: String,
    /// Ordered kind-Type parameters.
    pub parameters: Vec<String>,
    /// Exact native operations in defining order.
    pub operations: Vec<ForeignOperationDeclaration>,
}
/// State/result relationship authenticated independently of operation spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForeignResultRelation {
    /// Copied ordinary results have no native state dependency.
    Independent,
    /// Acquired state retains the selected effect parameter identities.
    Acquire {
        /// State nominal spelling.
        state: String,
        /// Error nominal spelling.
        error: String,
        /// Lifecycle report nominal spelling.
        report: String,
        /// Parameter positions retained by the successful state.
        retained_parameters: Vec<usize>,
    },
    /// Completion reports consume or retain exactly the owned state.
    Finish {
        /// State nominal spelling.
        state: String,
        /// Error nominal spelling.
        error: String,
        /// Lifecycle report nominal spelling.
        report: String,
    },
}
/// A registered operation scheme and its controlled role.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignOperationDeclaration {
    /// Defining operation spelling.
    pub name: String,
    /// Exact pure arrow in current Ash syntax.
    pub signature: String,
    /// Provider-phase authority required by the operation.
    pub role: ForeignOperationRole,
    /// Effect parameter that identifies the newly acquired or completed owner.
    pub owned_identity_position: usize,
    /// Tuple paths to borrowed states in the operation domain; an empty path is the whole domain.
    pub state_operands: Vec<Vec<usize>>,
    /// Whole domain argument positions retained after the operation.
    pub retained_arguments: Vec<usize>,
    /// State and independent-result contract.
    pub result: ForeignResultRelation,
}
/// Host-selected names for the sealed generic state-access primitive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignStateAccessDeclaration {
    /// Interface spelling; authority follows the bound InterfaceId.
    pub interface: String,
    /// Primitive method spelling; authority follows the bound MethodId.
    pub method: String,
}

/// A passive foundation method/operation scheme. It grants no executable role.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignFoundationOperationDeclaration {
    /// Defining operation or method spelling.
    pub name: String,
    /// Pure arrow parsed and resolved by the ordinary frontend.
    pub signature: String,
}

/// Authored sealed-layout contract, separate from provider-only state access.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignLayoutDeclaration {
    /// Interface spelling; private preparation authenticates its defining ID.
    pub name: String,
    /// Kind-Type payload binder of the interface.
    pub parameter: String,
    /// Nominal carrying the independent layout witness.
    pub witness: String,
    /// Exact witness-producing method, without a source implementation.
    pub method: ForeignFoundationOperationDeclaration,
}

/// Passive store/load contract. It is deliberately outside executable
/// `ForeignResultRelation`: incomplete storage authority cannot be Independent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignStorageDeclaration {
    /// Defining effect spelling.
    pub name: String,
    /// Ordered kind-Type effect parameters.
    pub parameters: Vec<String>,
    /// Effect coordinate denoting the storage owner.
    pub owner_parameter: usize,
    /// Effect coordinate denoting the stored payload type.
    pub payload_parameter: usize,
    /// Existing opaque resource-state family.
    pub state: String,
    /// Nonowning reference family.
    pub reference: String,
    /// Ordinary allocation report family with one success parameter.
    pub allocation_result: String,
    /// Independent ordinary refusal family.
    pub allocation_error: String,
    /// Successful allocation constructor, carrying the result parameter.
    pub allocated_constructor: String,
    /// Refusal constructor, carrying the independent error.
    pub refused_constructor: String,
    /// Exact store operation scheme.
    pub store: ForeignFoundationOperationDeclaration,
    /// Exact load operation scheme.
    pub load: ForeignFoundationOperationDeclaration,
}

/// Reviewed experimental foundation descriptions. Binding validates them
/// privately, then rejects before publishing any usable expanded module fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignFoundationDeclaration {
    /// Independent sealed layout interface and witness contract.
    pub layout: ForeignLayoutDeclaration,
    /// Owner/payload-indexed native storage contract.
    pub storage: ForeignStorageDeclaration,
}
/// Bridge-authored declarations. This is not an Ash source ABI declaration.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ForeignManifestSchema {
    /// Canonical native state and ordinary data families.
    pub types: Vec<ForeignTypeDeclaration>,
    /// Canonical native effects and controlled operations.
    pub effects: Vec<ForeignEffectDeclaration>,
    /// Optional sealed generic provider primitive.
    pub state_access: Option<ForeignStateAccessDeclaration>,
    /// Non-executable typed-storage preparation; never published as authority.
    pub foundation: Option<ForeignFoundationDeclaration>,
}
/// A rejected host registration; no entry is published on failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignRegistrationError {
    message: String,
    resource: bool,
}
impl ForeignRegistrationError {
    pub(crate) const fn is_resource_exhaustion(&self) -> bool {
        self.resource
    }
}
impl fmt::Display for ForeignRegistrationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl Error for ForeignRegistrationError {}
fn invalid(message: &str) -> ForeignRegistrationError {
    ForeignRegistrationError {
        message: message.to_owned(),
        resource: false,
    }
}
fn charge(
    work: &mut crate::types::TypeWorkBudget,
    amount: usize,
) -> Result<(), ForeignRegistrationError> {
    work.charge(amount).map_err(|()| ForeignRegistrationError {
        message: "foreign registration type-work budget exhausted".into(),
        resource: true,
    })
}
fn identifier(name: &str, upper: bool) -> bool {
    let mut bytes = name.bytes();
    bytes.next().is_some_and(|first| {
        if upper {
            first.is_ascii_uppercase()
        } else {
            first.is_ascii_lowercase()
        }
    }) && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}
fn type_fragment(text: &str) -> bool {
    !text.is_empty()
        && text.len() <= 4096
        && text
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"_ <>,()-".contains(&byte))
}

/// Immutable validated declaration source and manifest identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignManifest {
    path: String,
    id: ForeignRegistrationId,
    source: String,
    schema: ForeignManifestSchema,
    digest: [u8; 32],
}
impl ForeignManifest {
    /// Validates structural metadata and generates declarations for normal parsing.
    ///
    /// # Errors
    /// Rejects invalid reserved paths, names, roles, budgets, or declaration fragments.
    pub fn new(
        path: impl Into<String>,
        id: ForeignRegistrationId,
        schema: ForeignManifestSchema,
    ) -> Result<Self, ForeignRegistrationError> {
        let path = path.into();
        if !path
            .strip_prefix("@foreign.")
            .is_some_and(|tail| tail.split('.').all(|part| identifier(part, false)))
        {
            return Err(invalid(
                "foreign registration requires a full @foreign module path",
            ));
        }
        let declaration_count = schema
            .types
            .len()
            .checked_add(schema.effects.len())
            .and_then(|count| count.checked_add(2 * usize::from(schema.foundation.is_some())))
            .ok_or_else(|| invalid("foreign manifest declaration budget exceeded"))?;
        if declaration_count > 256 {
            return Err(invalid("foreign manifest declaration budget exceeded"));
        }
        let mut source = String::new();
        let mut names = HashSet::new();
        let mut constructor_names = HashSet::new();
        for ty in &schema.types {
            if !identifier(&ty.name, true)
                || !names.insert(ty.name.clone())
                || ty.parameters.len() > 32
                || ty
                    .parameters
                    .iter()
                    .any(|parameter| !identifier(parameter, true))
                || ty.constructors.len() > 256
            {
                return Err(invalid("invalid foreign nominal declaration"));
            }
            if ty.category == ForeignTypeCategory::State && ty.parameters.is_empty() {
                return Err(invalid("native state requires an owner identity parameter"));
            }
            if ty.category.is_opaque() != ty.constructors.is_empty() {
                return Err(invalid(
                    "opaque native states require no source constructors; ordinary data requires constructors",
                ));
            }
            validate_category(ty)?;
            source.push_str(if ty.category.is_opaque() {
                "pub opaque type "
            } else {
                "pub type "
            });
            source.push_str(&ty.name);
            append_parameters(&mut source, &ty.parameters);
            source.push_str(" = ");
            if ty.category.is_opaque() {
                source.push_str(&format!("HiddenNative{}\n", ty.name));
            } else {
                for (index, constructor) in ty.constructors.iter().enumerate() {
                    if !identifier(&constructor.name, true)
                        || !constructor_names.insert(constructor.name.clone())
                        || constructor
                            .payload
                            .as_ref()
                            .is_some_and(|payload| !type_fragment(payload))
                    {
                        return Err(invalid("invalid foreign codec constructor"));
                    }
                    if index > 0 {
                        source.push_str("| ");
                    }
                    source.push_str(&constructor.name);
                    if let Some(payload) = &constructor.payload {
                        source.push('(');
                        source.push_str(payload);
                        source.push(')');
                    }
                    source.push('\n');
                }
            }
        }
        for effect in &schema.effects {
            if !identifier(&effect.name, true)
                || !names.insert(effect.name.clone())
                || effect.parameters.is_empty()
                || effect.parameters.len() > 32
                || effect
                    .parameters
                    .iter()
                    .any(|parameter| !identifier(parameter, true))
                || effect.operations.is_empty()
                || effect.operations.len() > 256
            {
                return Err(invalid("invalid foreign effect declaration"));
            }
            source.push_str("pub effect ");
            source.push_str(&effect.name);
            append_parameters(&mut source, &effect.parameters);
            source.push_str(" {\n");
            let mut operations = HashSet::new();
            for operation in &effect.operations {
                if !identifier(&operation.name, false)
                    || !operations.insert(&operation.name)
                    || !type_fragment(&operation.signature)
                    || operation.owned_identity_position >= effect.parameters.len()
                    || operation.state_operands.len() > 32
                    || operation.state_operands.iter().any(|path| path.len() > 32)
                    || operation.retained_arguments.len() > 32
                {
                    return Err(invalid("invalid foreign operation metadata"));
                }
                if !matches!(
                    (&operation.role, &operation.result),
                    (
                        ForeignOperationRole::Acquire,
                        ForeignResultRelation::Acquire { .. }
                    ) | (
                        ForeignOperationRole::Borrow,
                        ForeignResultRelation::Independent
                    ) | (
                        ForeignOperationRole::Finish,
                        ForeignResultRelation::Finish { .. }
                    )
                ) {
                    return Err(invalid(
                        "foreign operation role disagrees with result relation",
                    ));
                }
                source.push_str(&operation.name);
                source.push_str(" : ");
                source.push_str(&operation.signature);
                source.push('\n');
            }
            source.push_str("}\n");
        }
        if let Some(access) = &schema.state_access {
            if !identifier(&access.interface, true)
                || !identifier(&access.method, false)
                || !names.insert(access.interface.clone())
            {
                return Err(invalid("invalid foreign state-access declaration"));
            }
            source.push_str(&format!(
                "pub interface {}<Q, State> where Q -> State {{\n{} : Q -> State\n}}\n",
                access.interface, access.method
            ));
        }
        append_foundation_source(&schema, &mut names, &mut source)?;
        if source.len() > 1_048_576 {
            return Err(invalid("foreign manifest source budget exceeded"));
        }
        let digest = manifest_digest(&path, id, &source, &schema);
        Ok(Self {
            path,
            id,
            source,
            schema,
            digest,
        })
    }
    /// Returns the full reserved import path.
    #[must_use]
    pub fn path(&self) -> &str {
        &self.path
    }
    /// Returns the host registration identity.
    #[must_use]
    pub const fn id(&self) -> ForeignRegistrationId {
        self.id
    }
    /// Returns generated passive declaration source.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }
    /// Returns a digest covering declaration source and relational metadata.
    #[must_use]
    pub const fn digest(&self) -> [u8; 32] {
        self.digest
    }
}
fn validate_category(declaration: &ForeignTypeDeclaration) -> Result<(), ForeignRegistrationError> {
    let count = declaration.parameters.len();
    let valid = match declaration.category {
        ForeignTypeCategory::Data | ForeignTypeCategory::State => true,
        ForeignTypeCategory::LayoutWitness { payload_parameter } => {
            count == 1 && payload_parameter < count
        }
        ForeignTypeCategory::Reference {
            owner_parameter,
            payload_parameter,
        } => {
            count == 2
                && owner_parameter < count
                && payload_parameter < count
                && owner_parameter != payload_parameter
                && declaration.parameters[owner_parameter]
                    != declaration.parameters[payload_parameter]
        }
    };
    if !valid {
        return Err(invalid("foreign category parameter coordinates differ"));
    }
    Ok(())
}

fn append_foundation_source(
    schema: &ForeignManifestSchema,
    names: &mut HashSet<String>,
    source: &mut String,
) -> Result<(), ForeignRegistrationError> {
    let Some(foundation) = &schema.foundation else {
        if schema.types.iter().any(|ty| ty.category.is_foundation()) {
            return Err(invalid(
                "typed foreign categories require a storage foundation",
            ));
        }
        return Ok(());
    };
    let layout = &foundation.layout;
    let storage = &foundation.storage;
    if !identifier(&layout.name, true)
        || !names.insert(layout.name.clone())
        || !identifier(&layout.parameter, true)
        || !identifier(&layout.method.name, false)
        || !type_fragment(&layout.method.signature)
        || !identifier(&storage.name, true)
        || !names.insert(storage.name.clone())
        || storage.parameters.len() != 2
        || storage
            .parameters
            .iter()
            .any(|parameter| !identifier(parameter, true))
        || storage.parameters[0] == storage.parameters[1]
        || storage.owner_parameter >= 2
        || storage.payload_parameter >= 2
        || storage.owner_parameter == storage.payload_parameter
        || !identifier(&storage.store.name, false)
        || !type_fragment(&storage.store.signature)
        || !identifier(&storage.load.name, false)
        || !type_fragment(&storage.load.signature)
        || storage.store.name == storage.load.name
    {
        return Err(invalid("invalid foreign storage foundation declaration"));
    }
    let find = |name: &str| schema.types.iter().find(|ty| ty.name == name);
    let witness =
        find(&layout.witness).ok_or_else(|| invalid("foreign layout witness category missing"))?;
    let reference =
        find(&storage.reference).ok_or_else(|| invalid("foreign reference category missing"))?;
    let state = find(&storage.state).ok_or_else(|| invalid("foreign storage state missing"))?;
    let report = find(&storage.allocation_result)
        .ok_or_else(|| invalid("foreign allocation report missing"))?;
    let error = find(&storage.allocation_error)
        .ok_or_else(|| invalid("foreign allocation error missing"))?;
    if !matches!(witness.category, ForeignTypeCategory::LayoutWitness { .. })
        || !matches!(reference.category, ForeignTypeCategory::Reference { .. })
        || state.category != ForeignTypeCategory::State
        || state.parameters.len() != 1
        || report.category != ForeignTypeCategory::Data
        || report.parameters.len() != 1
        || error.category != ForeignTypeCategory::Data
        || !error.parameters.is_empty()
        || report.constructors.len() != 2
        || report.constructors[0].name != storage.allocated_constructor
        || report.constructors[1].name != storage.refused_constructor
        || schema
            .types
            .iter()
            .filter(|ty| ty.category.is_foundation())
            .count()
            != 2
    {
        return Err(invalid("foreign storage foundation categories differ"));
    }
    source.push_str("pub interface ");
    source.push_str(&layout.name);
    source.push('<');
    source.push_str(&layout.parameter);
    source.push_str("> {\n");
    source.push_str(&layout.method.name);
    source.push_str(" : ");
    source.push_str(&layout.method.signature);
    source.push_str("\n}\npub effect ");
    source.push_str(&storage.name);
    append_parameters(source, &storage.parameters);
    source.push_str(" {\n");
    for operation in [&storage.store, &storage.load] {
        source.push_str(&operation.name);
        source.push_str(" : ");
        source.push_str(&operation.signature);
        source.push('\n');
    }
    source.push_str("}\n");
    Ok(())
}
fn append_parameters(source: &mut String, parameters: &[String]) {
    if !parameters.is_empty() {
        source.push('<');
        source.push_str(&parameters.join(", "));
        source.push('>');
    }
}
fn manifest_digest(
    path: &str,
    id: ForeignRegistrationId,
    source: &str,
    schema: &ForeignManifestSchema,
) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    // Frame path, registration identity, generated declarations, and schema.
    // Schema fields contain only ordered vectors and fixed enum/field order;
    // declaration order also determines canonical operation/constructor IDs.
    for component in [
        path.to_owned(),
        id.value().to_string(),
        source.to_owned(),
        format!("{schema:?}"),
    ] {
        hasher.update((component.len() as u64).to_le_bytes());
        hasher.update(component.as_bytes());
    }
    hasher.finalize().into()
}
/// An immutable map keyed by full absolute foreign module path.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ForeignRegistrations {
    entries: BTreeMap<String, Arc<ForeignManifest>>,
}
impl ForeignRegistrations {
    /// Admits a complete table atomically, rejecting repeated paths or registration IDs.
    /// # Errors
    /// Returns an error on duplicate path or host identity.
    pub fn new(
        manifests: impl IntoIterator<Item = ForeignManifest>,
    ) -> Result<Self, ForeignRegistrationError> {
        let mut entries = BTreeMap::new();
        let mut ids = HashSet::new();
        for manifest in manifests {
            if entries.len() >= 256
                || entries.contains_key(manifest.path())
                || !ids.insert(manifest.id())
            {
                return Err(invalid(
                    "duplicate foreign path/identity or registration table budget exceeded",
                ));
            }
            entries.insert(manifest.path.clone(), Arc::new(manifest));
        }
        Ok(Self { entries })
    }
    /// Looks up an exact path, with no spelling or filesystem fallback.
    #[must_use]
    pub fn get(&self, path: &str) -> Option<&Arc<ForeignManifest>> {
        self.entries.get(path)
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForeignModuleSource {
    pub admission: ForeignModuleAdmission,
    pub manifest: Arc<ForeignManifest>,
}
/// Canonical identity and provenance of one native state family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignStateFact {
    /// Opaque defining nominal.
    pub id: NominalTypeId,
    /// Ordered lineage positions.
    pub parameter_count: usize,
    /// State parameter that identifies its owner.
    pub owned_identity_position: usize,
    /// Defining provenance.
    pub origin: Origin,
}

/// Physical scalar encoding selected by an authenticated dictionary.
/// This descriptor alone grants no witness or foreign authority.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ForeignScalarEncoding {
    /// Zero bytes, alignment one.
    Unit,
    /// One byte, restricted to zero and one.
    Bool,
    /// Checked signed 64-bit little-endian two's-complement integer.
    Signed64,
}
impl ForeignScalarEncoding {
    fn payload_type(self) -> Type {
        match self {
            Self::Unit => Type::Unit,
            Self::Bool => Type::Bool,
            Self::Signed64 => Type::Int,
        }
    }
}

/// Qualified dictionary lookup identity; it does not authenticate a dictionary.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ForeignLayoutDictionaryId {
    interface: InterfaceId,
    ordinal: u8,
}

/// Inspectable pure-callable header copied from a canonical dictionary.
/// Consumers must authenticate the full dictionary against the original fact.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ForeignLayoutProducer {
    dictionary: ForeignLayoutDictionaryId,
    method: MethodId,
    witness: NominalTypeId,
    payload: ForeignScalarEncoding,
}
impl ForeignLayoutProducer {
    /// Returns the qualified dictionary lookup identity.
    #[must_use]
    pub const fn dictionary(self) -> ForeignLayoutDictionaryId {
        self.dictionary
    }
    /// Returns the original dictionary's defining module.
    /// This header does not replace canonical dictionary authentication.
    #[must_use]
    pub const fn module(self) -> crate::module::ModuleId {
        self.dictionary.interface.module()
    }
    /// Returns the original defining interface.
    #[must_use]
    pub const fn interface(self) -> InterfaceId {
        self.dictionary.interface
    }
    /// Returns the original defining witness method.
    #[must_use]
    pub const fn method(self) -> MethodId {
        self.method
    }
    /// Returns the original opaque witness family.
    #[must_use]
    pub const fn witness(self) -> NominalTypeId {
        self.witness
    }
    /// Returns the exact closed payload type represented by this header.
    #[must_use]
    pub fn payload_type(self) -> Type {
        self.payload.payload_type()
    }
    /// Returns the ordinary nominal witness type.
    #[must_use]
    pub fn witness_type(self) -> Type {
        Type::Application(
            Box::new(Type::Nominal(self.witness)),
            Box::new(self.payload_type()),
        )
    }
    /// Returns the pure witness-producing method type.
    #[must_use]
    pub fn producer_type(self) -> Type {
        Type::Function(Box::new(Type::Unit), Box::new(self.witness_type()))
    }

    #[cfg(test)]
    pub(crate) const fn with_header_for_test(
        self,
        method: MethodId,
        witness: NominalTypeId,
        payload: ForeignScalarEncoding,
    ) -> Self {
        Self {
            method,
            witness,
            payload,
            ..self
        }
    }
}

/// Complete immutable scalar dictionary bound to original foreign identities.
/// Construction is private to canonical foreign admission. Later graph layouts
/// must extend this checked representation rather than authorize numeric tags.
#[derive(Debug, Eq, PartialEq)]
pub struct ForeignLayoutDictionary {
    producer: ForeignLayoutProducer,
    payload_type: Type,
    encoding: ForeignScalarEncoding,
    size: usize,
    natural_alignment: usize,
}
impl ForeignLayoutDictionary {
    /// Returns its copied pure-callable header.
    #[must_use]
    pub const fn producer(&self) -> ForeignLayoutProducer {
        self.producer
    }
    /// Returns its exact canonical payload type.
    #[must_use]
    pub const fn payload_type(&self) -> &Type {
        &self.payload_type
    }
    /// Returns its validated native encoding.
    #[must_use]
    pub const fn encoding(&self) -> ForeignScalarEncoding {
        self.encoding
    }
    /// Returns the encoded scalar extent.
    #[must_use]
    pub const fn size(&self) -> usize {
        self.size
    }
    /// Returns the encoded scalar natural alignment.
    #[must_use]
    pub const fn natural_alignment(&self) -> usize {
        self.natural_alignment
    }
}

/// Original sealed Layout authority and its finite scalar dictionary table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignLayoutFact {
    interface: InterfaceId,
    method: MethodId,
    witness: NominalTypeId,
    payload_parameter: TypeVariableId,
    dictionaries: [Arc<ForeignLayoutDictionary>; 3],
}
impl ForeignLayoutFact {
    /// Returns the sealed defining interface.
    #[must_use]
    pub const fn interface(&self) -> InterfaceId {
        self.interface
    }
    /// Returns the original witness-producing method.
    #[must_use]
    pub const fn method(&self) -> MethodId {
        self.method
    }
    /// Returns the opaque witness nominal.
    #[must_use]
    pub const fn witness(&self) -> NominalTypeId {
        self.witness
    }
    /// Returns the canonical interface payload binder.
    #[must_use]
    pub const fn payload_parameter(&self) -> TypeVariableId {
        self.payload_parameter
    }
    /// Resolves and checks the entire header, never just its ordinal.
    #[must_use]
    pub fn dictionary_for_producer(
        &self,
        producer: ForeignLayoutProducer,
    ) -> Option<Arc<ForeignLayoutDictionary>> {
        if producer.interface() != self.interface {
            return None;
        }
        let dictionary = self
            .dictionaries
            .get(usize::from(producer.dictionary.ordinal))?;
        (dictionary.producer == producer).then(|| Arc::clone(dictionary))
    }
    /// Derives only the admitted closed scalar payload goals.
    #[must_use]
    pub fn dictionary_for_payload(&self, payload: &Type) -> Option<Arc<ForeignLayoutDictionary>> {
        self.dictionaries
            .iter()
            .find(|dictionary| &dictionary.payload_type == payload)
            .map(Arc::clone)
    }
}

/// Exact canonical owner/payload coordinates and store/load result families.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignStorageFact {
    effect: EffectId,
    store: OperationId,
    load: OperationId,
    state: NominalTypeId,
    witness: NominalTypeId,
    reference: NominalTypeId,
    report: NominalTypeId,
    error: NominalTypeId,
    allocated_constructor: ConstructorId,
    refused_constructor: ConstructorId,
    owner_parameter: usize,
    payload_parameter: usize,
    reference_owner_parameter: usize,
    reference_payload_parameter: usize,
}
macro_rules! foreign_storage_readers {
    ($($name:ident : $ty:ty),* $(,)?) => {
        impl ForeignStorageFact {
            $(#[doc = concat!("Returns the canonical ", stringify!($name), " role.")]
            #[must_use]
            pub const fn $name(&self) -> $ty { self.$name })*
        }
    };
}
foreign_storage_readers! {
    effect: EffectId, store: OperationId, load: OperationId,
    state: NominalTypeId, witness: NominalTypeId, reference: NominalTypeId,
    report: NominalTypeId, error: NominalTypeId,
    allocated_constructor: ConstructorId, refused_constructor: ConstructorId,
    owner_parameter: usize, payload_parameter: usize,
    reference_owner_parameter: usize, reference_payload_parameter: usize,
}
/// Canonical lifecycle/result relation, with no source-name authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForeignResultFact {
    /// Copied independent data.
    Independent,
    /// Successful publication retains its actual payload; refusal is independent.
    Store {
        /// Defining storage contract; actual owner/payload come from this call.
        storage: EffectId,
    },
    /// Loads recover the selected object's actual stored payload relation.
    Load {
        /// Defining storage contract; never an operation-spelling convention.
        storage: EffectId,
    },
    /// Guarded acquired state and distinct error/report families.
    Acquire {
        /// Native state identity.
        state: NominalTypeId,
        /// Error identity.
        error: NominalTypeId,
        /// Lifecycle report identity.
        report: NominalTypeId,
        /// Acquired/refused codec alternatives in order.
        constructors: Vec<ConstructorId>,
        /// Dependency parameters retained by acquired state.
        retained_parameters: Vec<usize>,
    },
    /// Consumed/retained owned-state postcondition.
    Finish {
        /// Native state identity.
        state: NominalTypeId,
        /// Error identity.
        error: NominalTypeId,
        /// Lifecycle report identity.
        report: NominalTypeId,
        /// Consumed/consumed-failure/retained alternatives in order.
        constructors: Vec<ConstructorId>,
    },
}
/// A state operand's defining type and mapping to effect parameter lineage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignStateOperandFact {
    /// Tuple path within the operation domain.
    pub path: Vec<usize>,
    /// Native state nominal.
    pub state: NominalTypeId,
    /// Effect coordinates for each state type argument.
    pub lineage: Vec<usize>,
}
/// Canonical registered operation and its exact resolved scheme.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignOperationFact {
    /// Defining operation identity.
    pub id: OperationId,
    /// Exact controlled role.
    pub role: ForeignOperationRole,
    /// Owned effect identity coordinate.
    pub owned_identity_position: usize,
    /// Borrowed state domain paths.
    pub state_operands: Vec<Vec<usize>>,
    /// Bound current/enclosing state lineage.
    pub state_lineage: Vec<ForeignStateOperandFact>,
    /// Retained whole domain arguments.
    pub retained_arguments: Vec<usize>,
    /// Result relationship schema.
    pub result: ForeignResultFact,
    /// Exact resolved value type.
    pub signature: Type,
    /// Defining provenance.
    pub origin: Origin,
}
/// Authenticated provider primitive identities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignStateAccessFact {
    /// Sealed defining interface.
    pub interface: InterfaceId,
    /// Controlled method.
    pub method: MethodId,
    /// Defining provenance.
    pub origin: Origin,
}
/// Body-free foreign authority retained through checking, imports and linking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ForeignModuleFact {
    canonical_registry: Arc<ResolvedRegistry>,
    canonical_interfaces: Vec<ResolvedInterfaceDeclaration>,
    canonical_admission: ForeignModuleAdmission,
    manifest: Arc<ForeignManifest>,

    /// Loader-authenticated admission.
    pub admission: ForeignModuleAdmission,
    /// Opaque state identities.
    pub states: Vec<ForeignStateFact>,
    /// Canonical data families by codec role spelling.
    pub data_types: BTreeMap<String, NominalTypeId>,
    /// Canonical codec constructors.
    pub constructors: BTreeMap<String, ConstructorId>,
    /// Registered effect identities.
    pub effects: Vec<EffectId>,
    /// Controlled operations.
    pub operations: Vec<ForeignOperationFact>,
    /// Optional provider primitive.
    pub state_access: Option<ForeignStateAccessFact>,
    /// Optional sealed Layout authority and immutable dictionaries.
    pub layout: Option<ForeignLayoutFact>,
    /// Optional authenticated nonowning storage contract.
    pub storage: Option<ForeignStorageFact>,
}

fn discard_foreign_layout_iteratively(layout: ForeignLayoutFact) {
    for dictionary in layout.dictionaries {
        if let Ok(dictionary) = Arc::try_unwrap(dictionary) {
            crate::types::discard_type_iteratively(dictionary.payload_type);
        }
    }
}

impl Drop for ForeignModuleFact {
    fn drop(&mut self) {
        if let Some(layout) = self.layout.take() {
            discard_foreign_layout_iteratively(layout);
        }
        for interface in self.canonical_interfaces.drain(..) {
            crate::resolved::discard_resolved_interface_iteratively(interface);
        }
        for operation in self.operations.drain(..) {
            crate::types::discard_type_iteratively(operation.signature);
            crate::source::discard_origin_iteratively(operation.origin);
        }
        for state in self.states.drain(..) {
            crate::source::discard_origin_iteratively(state.origin);
        }
        if let Some(access) = self.state_access.take() {
            crate::source::discard_origin_iteratively(access.origin);
        }
        for admission in [&mut self.admission, &mut self.canonical_admission] {
            let placeholder = Origin::Source(admission.origin.primary_span());
            crate::source::discard_origin_iteratively(std::mem::replace(
                &mut admission.origin,
                placeholder,
            ));
        }
    }
}

/// Native self-proof cache confined to one independent admission. Entries can
/// be retained only by authenticating the exact immutable original allocation.
/// Shared ownership keeps that allocation alive across moved source drafts;
/// these facts own declarations, never native resource guards.
#[derive(Default)]
pub(crate) struct NativeAuthenticationMemo {
    facts: Vec<Arc<ForeignModuleFact>>,
}

pub(crate) type NativeAuthenticationSession = std::cell::RefCell<NativeAuthenticationMemo>;

impl NativeAuthenticationMemo {
    pub(crate) fn authenticate(
        &mut self,
        fact: &Arc<ForeignModuleFact>,
        work: &mut crate::types::TypeWorkBudget,
    ) -> Result<(), ForeignRegistrationError> {
        charge(work, self.facts.len())?;
        if self
            .facts
            .iter()
            .any(|original| Arc::ptr_eq(original, fact))
        {
            return Ok(());
        }
        fact.authenticate(work)?;
        // Retain one vector entry and one shared allocation handle.
        charge(work, 2)?;
        self.facts
            .try_reserve_exact(1)
            .map_err(|_| ForeignRegistrationError {
                message: "foreign authentication memo allocation refused".into(),
                resource: true,
            })?;
        self.facts.push(Arc::clone(fact));
        Ok(())
    }
}

impl ForeignModuleFact {
    /// Borrows the exact immutable manifest entry admitted by the source loader.
    #[must_use]
    pub fn manifest(&self) -> &Arc<ForeignManifest> {
        &self.manifest
    }

    fn set_layout(&mut self, layout: ForeignLayoutFact) {
        if let Some(displaced) = self.layout.replace(layout) {
            discard_foreign_layout_iteratively(displaced);
        }
    }

    fn set_state_access(&mut self, access: ForeignStateAccessFact) {
        if let Some(displaced) = self.state_access.replace(access) {
            crate::source::discard_origin_iteratively(displaced.origin);
        }
    }

    pub(crate) fn authenticate(
        &self,
        work: &mut crate::types::TypeWorkBudget,
    ) -> Result<(), ForeignRegistrationError> {
        if self.admission != self.canonical_admission {
            return Err(invalid("foreign admission certificate changed"));
        }
        let source = ForeignModuleSource {
            admission: self.admission.clone(),
            manifest: Arc::clone(&self.manifest),
        };
        let expected = source.bind(
            &self.canonical_registry,
            self.canonical_registry.effects(),
            &self.canonical_interfaces,
            work,
        )?;
        charge(work, self.operations.len())?;
        for operation in &self.operations {
            crate::types::charge_type_cells(&operation.signature, work).map_err(|()| {
                ForeignRegistrationError {
                    message: "foreign registration type work exhausted".into(),
                    resource: true,
                }
            })?;
        }
        if expected.as_ref() != self {
            return Err(invalid(
                "foreign registration certificate disagrees with admitted declarations",
            ));
        }
        Ok(())
    }
    pub(crate) fn canonical_registry(&self) -> &ResolvedRegistry {
        &self.canonical_registry
    }
    pub(crate) fn canonical_interfaces(&self) -> &[ResolvedInterfaceDeclaration] {
        &self.canonical_interfaces
    }
}
impl ForeignModuleSource {
    pub(crate) fn bind(
        &self,
        registry: &Arc<ResolvedRegistry>,
        effects: &[ResolvedEffectDeclaration],
        interfaces: &[ResolvedInterfaceDeclaration],
        work: &mut crate::types::TypeWorkBudget,
    ) -> Result<Arc<ForeignModuleFact>, ForeignRegistrationError> {
        if self.admission.registration_id != self.manifest.id()
            || self.admission.manifest_digest != self.manifest.digest()
        {
            return Err(invalid("foreign manifest admission identity differs"));
        }
        charge(
            work,
            registry
                .nominals()
                .len()
                .saturating_add(effects.len())
                .saturating_add(interfaces.len()),
        )?;
        for interface in interfaces {
            charge(
                work,
                interface
                    .parameters
                    .len()
                    .saturating_add(interface.methods.len()),
            )?;
            for method in &interface.methods {
                crate::types::charge_type_cells(&method.annotation.ty, work).map_err(|()| {
                    ForeignRegistrationError {
                        message: "foreign registration type-work budget exhausted".into(),
                        resource: true,
                    }
                })?;
            }
        }
        let mut fact = ForeignModuleFact {
            canonical_registry: Arc::clone(registry),
            canonical_interfaces: interfaces.to_vec(),
            canonical_admission: self.admission.clone(),
            manifest: Arc::clone(&self.manifest),
            admission: self.admission.clone(),
            states: Vec::new(),
            data_types: BTreeMap::new(),
            constructors: BTreeMap::new(),
            effects: Vec::new(),
            operations: Vec::new(),
            state_access: None,
            layout: None,
            storage: None,
        };
        let foundation = self.manifest.schema.foundation.as_ref();
        let mut foundation_types = FoundationTypeBindings::default();
        if registry.nominals().len() != self.manifest.schema.types.len()
            || effects.len()
                != self.manifest.schema.effects.len() + usize::from(foundation.is_some())
            || interfaces.len()
                != usize::from(self.manifest.schema.state_access.is_some())
                    + usize::from(foundation.is_some())
        {
            return Err(invalid("foreign declarations disagree with manifest"));
        }
        for declaration in &self.manifest.schema.types {
            charge(
                work,
                declaration
                    .parameters
                    .len()
                    .saturating_add(declaration.constructors.len())
                    .saturating_add(1),
            )?;
            let nominal = registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == declaration.name)
                .ok_or_else(|| invalid("foreign type missing"))?;
            let parameters = registry
                .nominal_parameters(nominal.id)
                .ok_or_else(|| invalid("foreign type parameters missing"))?;
            if parameters.len() != declaration.parameters.len()
                || nominal.id.module() != fact.admission.module_id
            {
                return Err(invalid("foreign type identity or arity differs"));
            }
            if let Some(foundation) = foundation {
                validate_foundation_nominal(registry, nominal, declaration, &self.admission, work)?;
                foundation_types.retain(foundation, nominal, declaration.category);
            }
            if declaration.category == ForeignTypeCategory::State {
                fact.states.push(ForeignStateFact {
                    id: nominal.id,
                    parameter_count: parameters.len(),
                    owned_identity_position: 0,
                    origin: nominal.origin.clone(),
                });
            } else if declaration.category == ForeignTypeCategory::Data {
                fact.data_types.insert(declaration.name.clone(), nominal.id);
                if nominal.constructors.len() != declaration.constructors.len() {
                    return Err(invalid("foreign constructor count differs"));
                }
                for (id, constructor) in nominal.constructors.iter().zip(&declaration.constructors)
                {
                    let actual = registry
                        .constructor(*id)
                        .ok_or_else(|| invalid("foreign constructor missing"))?;
                    if actual.spelling != constructor.name || actual.owner != nominal.id {
                        return Err(invalid("foreign constructor identity differs"));
                    }
                    fact.constructors.insert(constructor.name.clone(), *id);
                }
            }
        }
        for declaration in &self.manifest.schema.effects {
            let effect = effects
                .iter()
                .find(|effect| effect.spelling == declaration.name)
                .ok_or_else(|| invalid("foreign effect missing"))?;
            if effect.operations.len() != declaration.operations.len()
                || effect.parameters.len() != declaration.parameters.len()
                || effect.id.module() != fact.admission.module_id
            {
                return Err(invalid("foreign effect identity or arity differs"));
            }
            fact.effects.push(effect.id);
            for (operation, metadata) in effect.operations.iter().zip(&declaration.operations) {
                if operation.spelling != metadata.name {
                    return Err(invalid("foreign operation identity differs"));
                }
                charge(
                    work,
                    metadata
                        .state_operands
                        .iter()
                        .map(Vec::len)
                        .sum::<usize>()
                        .saturating_add(metadata.retained_arguments.len())
                        .saturating_add(effect.parameters.len())
                        .saturating_add(1),
                )?;
                validate_operation(
                    registry,
                    &fact,
                    effect,
                    &operation.annotation.ty,
                    metadata,
                    work,
                )?;
                fact.operations.push(ForeignOperationFact {
                    id: operation.id,
                    role: metadata.role,
                    owned_identity_position: metadata.owned_identity_position,
                    state_operands: metadata.state_operands.clone(),
                    state_lineage: bind_state_lineage(&operation.annotation.ty, metadata, effect),
                    retained_arguments: metadata.retained_arguments.clone(),
                    result: bind_result(&metadata.result, registry, &fact),
                    signature: crate::types::clone_type_with_budget(&operation.annotation.ty, work)
                        .map_err(|()| ForeignRegistrationError {
                            message: "foreign registration type-work budget exhausted".into(),
                            resource: true,
                        })?,
                    origin: operation.origin.clone(),
                });
            }
        }
        if let Some(declaration) = &self.manifest.schema.state_access {
            let interface = interfaces
                .iter()
                .find(|interface| interface.spelling == declaration.interface)
                .ok_or_else(|| invalid("foreign state-access interface missing"))?;
            let [method] = interface.methods.as_ref() else {
                return Err(invalid("foreign state-access method count differs"));
            };
            let [q, state] = interface.parameters.as_ref() else {
                return Err(invalid("foreign state-access arity differs"));
            };
            let determination = interface
                .determination
                .as_ref()
                .ok_or_else(|| invalid("foreign state-access determination missing"))?;
            if method.spelling != declaration.method
                || method.annotation.ty
                    != Type::function(Type::Variable(q.id), Type::Variable(state.id))
                || determination.determinant.parameters.len() != 1
                || determination.dependent.parameters.len() != 1
                || determination.determinant.parameters[0].id != q.id
                || determination.dependent.parameters[0].id != state.id
            {
                return Err(invalid("foreign state-access scheme differs"));
            }
            fact.set_state_access(ForeignStateAccessFact {
                interface: interface.id,
                method: method.id,
                origin: interface.origin.clone(),
            });
        }
        if let Some(declaration) = foundation {
            let prepared = prepare_foreign_foundation(
                registry,
                &fact,
                effects,
                interfaces,
                declaration,
                foundation_types,
                work,
            )?;
            charge(work, 3)?;
            fact.effects
                .try_reserve(1)
                .map_err(|_| ForeignRegistrationError {
                    message: "foreign storage fact reservation refused".into(),
                    resource: true,
                })?;
            fact.operations
                .try_reserve(2)
                .map_err(|_| ForeignRegistrationError {
                    message: "foreign storage operation reservation refused".into(),
                    resource: true,
                })?;
            fact.effects.push(prepared.storage.effect());
            for (operation, result) in prepared.declaration.operations.iter().zip([
                ForeignResultFact::Store {
                    storage: prepared.storage.effect(),
                },
                ForeignResultFact::Load {
                    storage: prepared.storage.effect(),
                },
            ]) {
                let signature =
                    crate::types::clone_type_with_budget(&operation.annotation.ty, work).map_err(
                        |()| ForeignRegistrationError {
                            message: "foreign registration type-work budget exhausted".into(),
                            resource: true,
                        },
                    )?;
                fact.operations.push(ForeignOperationFact {
                    id: operation.id,
                    role: ForeignOperationRole::Borrow,
                    owned_identity_position: prepared.storage.owner_parameter(),
                    state_operands: vec![vec![0]],
                    state_lineage: vec![ForeignStateOperandFact {
                        path: vec![0],
                        state: prepared.storage.state(),
                        lineage: vec![prepared.storage.owner_parameter()],
                    }],
                    retained_arguments: vec![],
                    result,
                    signature,
                    origin: operation.origin.clone(),
                });
            }
            fact.set_layout(prepared.layout);
            fact.storage = Some(prepared.storage);
        }
        Ok(Arc::new(fact))
    }
}
// Selected in the original nominal-binding pass. Names locate authored roles;
// all later checks use these canonical declarations and their qualified IDs.
#[derive(Default)]
struct FoundationTypeBindings<'a> {
    state: Option<&'a ResolvedNominalType>,
    witness: Option<&'a ResolvedNominalType>,
    reference: Option<&'a ResolvedNominalType>,
    reference_coordinates: Option<(usize, usize)>,
    report: Option<&'a ResolvedNominalType>,
    error: Option<&'a ResolvedNominalType>,
}
impl<'a> FoundationTypeBindings<'a> {
    fn retain(
        &mut self,
        declaration: &ForeignFoundationDeclaration,
        nominal: &'a ResolvedNominalType,
        category: ForeignTypeCategory,
    ) {
        if nominal.spelling == declaration.storage.reference
            && let ForeignTypeCategory::Reference {
                owner_parameter,
                payload_parameter,
            } = category
        {
            self.reference_coordinates = Some((owner_parameter, payload_parameter));
        }
        for (name, slot) in [
            (&declaration.storage.state, &mut self.state),
            (&declaration.layout.witness, &mut self.witness),
            (&declaration.storage.reference, &mut self.reference),
            (&declaration.storage.allocation_result, &mut self.report),
            (&declaration.storage.allocation_error, &mut self.error),
        ] {
            if nominal.spelling == *name {
                *slot = Some(nominal);
            }
        }
    }
}

// Private preparation borrows original operation declarations and owns only
// checked flat roles plus closed scalar dictionaries.
struct PreparedForeignFoundation<'a> {
    layout: ForeignLayoutFact,
    storage: ForeignStorageFact,
    declaration: &'a ResolvedEffectDeclaration,
}

fn validate_foundation_parameters(
    registry: &ResolvedRegistry,
    parameters: &[ResolvedTypeVariable],
    spellings: &[String],
    admission: &ForeignModuleAdmission,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<(), ForeignRegistrationError> {
    charge(
        work,
        parameters
            .len()
            .saturating_mul(parameters.len().saturating_add(1)),
    )?;
    if parameters.len() != spellings.len() {
        return Err(invalid("foreign foundation parameter arity differs"));
    }
    for (index, (parameter, spelling)) in parameters.iter().zip(spellings).enumerate() {
        if parameter.kind != Kind::Type
            || parameter.spelling != *spelling
            || parameter.id.module() != Some(admission.module_id)
            || parameter.origin.primary_span().source() != admission.origin.primary_span().source()
            || registry.type_variable(parameter.id) != Some(parameter)
            || parameters[..index].iter().any(|previous| {
                previous.id == parameter.id || previous.spelling == parameter.spelling
            })
        {
            return Err(invalid("foreign foundation parameter identity differs"));
        }
    }
    Ok(())
}

fn validate_foundation_nominal(
    registry: &ResolvedRegistry,
    nominal: &ResolvedNominalType,
    declaration: &ForeignTypeDeclaration,
    admission: &ForeignModuleAdmission,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<(), ForeignRegistrationError> {
    if nominal.id.module() != admission.module_id
        || nominal.declaration_kind != ResolvedNominalDeclarationKind::Data
        || nominal.representation.is_some()
        || nominal.representation_provenance.is_some()
        || nominal.origin.primary_span().source() != admission.origin.primary_span().source()
    {
        return Err(invalid("foreign foundation nominal identity differs"));
    }
    validate_foundation_parameters(
        registry,
        registry
            .nominal_parameters(nominal.id)
            .ok_or_else(|| invalid("foreign foundation parameters missing"))?,
        &declaration.parameters,
        admission,
        work,
    )?;
    let expected_count = if declaration.category.is_opaque() {
        1
    } else {
        declaration.constructors.len()
    };
    if nominal.constructors.len() != expected_count {
        return Err(invalid("foreign foundation constructor count differs"));
    }
    for (ordinal, id) in nominal.constructors.iter().enumerate() {
        charge(work, 1)?;
        let constructor = registry
            .constructor(*id)
            .ok_or_else(|| invalid("foreign foundation constructor missing"))?;
        if constructor.id != *id
            || id.owner() != nominal.id
            || id.constructor() as usize != ordinal
            || constructor.owner != nominal.id
            || constructor.origin.primary_span().source()
                != admission.origin.primary_span().source()
        {
            return Err(invalid("foreign foundation constructor identity differs"));
        }
        if declaration.category.is_opaque()
            && (constructor.spelling != format!("HiddenNative{}", declaration.name)
                || constructor.payload.is_some())
        {
            return Err(invalid("foreign foundation opaque representation differs"));
        }
    }
    Ok(())
}

fn nominal_argument(ty: &Type, id: NominalTypeId) -> Option<&Type> {
    let Type::Application(head, argument) = ty else {
        return None;
    };
    matches!(head.as_ref(), Type::Nominal(actual) if *actual == id).then_some(argument.as_ref())
}
fn nominal_arguments(ty: &Type, id: NominalTypeId) -> Option<[&Type; 2]> {
    let Type::Application(head, second) = ty else {
        return None;
    };
    Some([nominal_argument(head, id)?, second.as_ref()])
}
fn is_variable(ty: &Type, id: TypeVariableId) -> bool {
    matches!(ty, Type::Variable(actual) if *actual == id)
}
fn foundation_span_contains(outer: Span, inner: Span) -> bool {
    outer.source() == inner.source()
        && outer.range().start() <= inner.range().start()
        && inner.range().end() <= outer.range().end()
}

fn prepare_foreign_foundation<'a>(
    registry: &ResolvedRegistry,
    fact: &ForeignModuleFact,
    effects: &'a [ResolvedEffectDeclaration],
    interfaces: &'a [ResolvedInterfaceDeclaration],
    declaration: &ForeignFoundationDeclaration,
    types: FoundationTypeBindings<'_>,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<PreparedForeignFoundation<'a>, ForeignRegistrationError> {
    let FoundationTypeBindings {
        state: Some(state),
        witness: Some(witness),
        reference: Some(reference),
        reference_coordinates: Some((reference_owner, reference_payload)),
        report: Some(report),
        error: Some(error),
    } = types
    else {
        return Err(invalid("foreign foundation canonical roles missing"));
    };
    let layout = interfaces
        .iter()
        .find(|interface| interface.spelling == declaration.layout.name)
        .ok_or_else(|| invalid("foreign layout interface missing"))?;
    let storage = effects
        .iter()
        .find(|effect| effect.spelling == declaration.storage.name)
        .ok_or_else(|| invalid("foreign storage effect missing"))?;
    charge(
        work,
        interfaces
            .len()
            .saturating_add(effects.len())
            .saturating_add(storage.operations.len()),
    )?;
    if layout.id.module() != fact.admission.module_id
        || !layout.public
        || layout.origin.primary_span().source() != fact.admission.origin.primary_span().source()
        || layout.span != layout.origin.primary_span()
        || layout.determination.is_some()
    {
        return Err(invalid("foreign layout interface identity differs"));
    }
    validate_foundation_parameters(
        registry,
        &layout.parameters,
        std::slice::from_ref(&declaration.layout.parameter),
        &fact.admission,
        work,
    )?;
    let [method] = layout.methods.as_ref() else {
        return Err(invalid("foreign layout method count differs"));
    };
    let Type::Function(domain, result) = &method.annotation.ty else {
        return Err(invalid("foreign layout method requires one pure arrow"));
    };
    let payload = layout.parameters[0].id;
    if method.id.interface() != layout.id
        || method.id.declaration() != 0
        || method.spelling != declaration.layout.method.name
        || !method.type_parameters.is_empty()
        || method.has_explicit_type_parameters
        || method.span != method.origin.primary_span()
        || method.span.source() != layout.span.source()
        || method.annotation.span.source() != layout.span.source()
        || method.annotation.origin.primary_span().source() != layout.span.source()
        || !matches!(domain.as_ref(), Type::Unit)
        || !nominal_argument(result, witness.id)
            .is_some_and(|argument| is_variable(argument, payload))
    {
        return Err(invalid("foreign layout method scheme differs"));
    }
    for operation in &storage.operations {
        crate::types::charge_type_cells(&operation.annotation.ty, work).map_err(|()| {
            ForeignRegistrationError {
                message: "foreign registration type-work budget exhausted".into(),
                resource: true,
            }
        })?;
    }
    if storage.id.module() != fact.admission.module_id
        || !storage.public
        || storage.origin.primary_span().source() != fact.admission.origin.primary_span().source()
        || !foundation_span_contains(storage.span, storage.origin.primary_span())
        || registry.effect(storage.id) != Some(storage)
    {
        return Err(invalid("foreign storage effect identity differs"));
    }
    validate_foundation_parameters(
        registry,
        &storage.parameters,
        &declaration.storage.parameters,
        &fact.admission,
        work,
    )?;
    let [store, load] = storage.operations.as_ref() else {
        return Err(invalid("foreign storage operation count differs"));
    };
    for (ordinal, (operation, authored)) in [
        (store, &declaration.storage.store),
        (load, &declaration.storage.load),
    ]
    .into_iter()
    .enumerate()
    {
        if operation.id.owner() != storage.id
            || operation.id.operation() as usize != ordinal
            || operation.spelling != authored.name
            || !foundation_span_contains(operation.span, operation.origin.primary_span())
            || operation.span.source() != storage.span.source()
            || operation.annotation.span.source() != storage.span.source()
            || operation.annotation.origin.primary_span().source() != storage.span.source()
        {
            return Err(invalid("foreign storage operation identity differs"));
        }
    }
    let owner_position = declaration.storage.owner_parameter;
    let payload_position = declaration.storage.payload_parameter;
    let owner = storage.parameters[owner_position].id;
    let payload = storage.parameters[payload_position].id;
    let valid_state = |ty: &Type| {
        nominal_argument(ty, state.id).is_some_and(|argument| is_variable(argument, owner))
    };
    let valid_witness = |ty: &Type| {
        nominal_argument(ty, witness.id).is_some_and(|argument| is_variable(argument, payload))
    };
    let valid_reference = |ty: &Type| {
        nominal_arguments(ty, reference.id).is_some_and(|arguments| {
            is_variable(arguments[reference_owner], owner)
                && is_variable(arguments[reference_payload], payload)
        })
    };
    let Type::Function(store_domain, store_result) = &store.annotation.ty else {
        return Err(invalid("foreign store requires one pure arrow"));
    };
    let Type::Tuple(store_fields) = store_domain.as_ref() else {
        return Err(invalid("foreign store domain differs"));
    };
    let Type::Function(load_domain, load_result) = &load.annotation.ty else {
        return Err(invalid("foreign load requires one pure arrow"));
    };
    let Type::Tuple(load_fields) = load_domain.as_ref() else {
        return Err(invalid("foreign load domain differs"));
    };
    charge(work, 32)?;
    if store_fields.len() != 4
        || load_fields.len() != 3
        || !valid_state(&store_fields[0])
        || !valid_witness(&store_fields[1])
        || !matches!(&store_fields[2], Type::Int)
        || !is_variable(&store_fields[3], payload)
        || !nominal_argument(store_result, report.id).is_some_and(valid_reference)
        || !valid_state(&load_fields[0])
        || !valid_witness(&load_fields[1])
        || !valid_reference(&load_fields[2])
        || !is_variable(load_result, payload)
    {
        return Err(invalid(
            "foreign storage owner, witness, reference or payload scheme differs",
        ));
    }
    let [success_id, refused_id] = report.constructors.as_ref() else {
        return Err(invalid(
            "foreign allocation report constructor count differs",
        ));
    };
    let success = registry
        .constructor(*success_id)
        .ok_or_else(|| invalid("foreign allocation success missing"))?;
    let refused = registry
        .constructor(*refused_id)
        .ok_or_else(|| invalid("foreign allocation refusal missing"))?;
    let parameters = registry
        .nominal_parameters(report.id)
        .ok_or_else(|| invalid("foreign allocation report parameter missing"))?;
    if parameters.len() != 1
        || success.spelling != declaration.storage.allocated_constructor
        || refused.spelling != declaration.storage.refused_constructor
        || !success
            .payload
            .as_ref()
            .is_some_and(|ty| is_variable(ty, parameters[0].id))
        || !matches!(refused.payload.as_ref(), Some(Type::Nominal(id)) if *id == error.id)
    {
        return Err(invalid("foreign allocation report scheme differs"));
    }
    validate_independent_data(registry, fact, storage, &Type::Nominal(error.id), work)?;
    validate_foundation_data_arities(registry, &Type::Nominal(error.id), work)?;
    // The finite table is defined by this registered native serialization
    // policy, not by a source name, value, or unchecked producer annotation.
    charge(work, 18 + 3 * 10)?;
    let policies = [
        (ForeignScalarEncoding::Unit, 0, 1),
        (ForeignScalarEncoding::Bool, 1, 1),
        (ForeignScalarEncoding::Signed64, 8, 8),
    ];
    let dictionaries = std::array::from_fn(|ordinal| {
        let (encoding, size, natural_alignment) = policies[ordinal];
        Arc::new(ForeignLayoutDictionary {
            producer: ForeignLayoutProducer {
                dictionary: ForeignLayoutDictionaryId {
                    interface: layout.id,
                    ordinal: ordinal as u8,
                },
                method: method.id,
                witness: witness.id,
                payload: encoding,
            },
            payload_type: encoding.payload_type(),
            encoding,
            size,
            natural_alignment,
        })
    });
    Ok(PreparedForeignFoundation {
        layout: ForeignLayoutFact {
            interface: layout.id,
            method: method.id,
            witness: witness.id,
            payload_parameter: layout.parameters[0].id,
            dictionaries,
        },
        storage: ForeignStorageFact {
            effect: storage.id,
            store: store.id,
            load: load.id,
            state: state.id,
            witness: witness.id,
            reference: reference.id,
            report: report.id,
            error: error.id,
            allocated_constructor: *success_id,
            refused_constructor: *refused_id,
            owner_parameter: owner_position,
            payload_parameter: payload_position,
            reference_owner_parameter: reference_owner,
            reference_payload_parameter: reference_payload,
        },
        declaration: storage,
    })
}

// Binding precedes ordinary kind checking. The unsupported-execution boundary
// must not conceal an ill-kinded refusal family inside an otherwise valid
// foundation. Traverse whole nominal applications, never their partial heads.
fn validate_foundation_data_arities(
    registry: &ResolvedRegistry,
    root: &Type,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<(), ForeignRegistrationError> {
    let mut pending = vec![root];
    let mut visited = HashSet::new();
    while let Some(ty) = pending.pop() {
        charge(work, 1)?;
        let mut head = ty;
        let mut argument_count = 0usize;
        while let Type::Application(function, argument) = head {
            charge(work, 1)?;
            argument_count = argument_count.saturating_add(1);
            pending.push(argument.as_ref());
            head = function;
        }
        match head {
            Type::Nominal(id) => {
                let parameters = registry
                    .nominal_parameters(*id)
                    .ok_or_else(|| invalid("foreign foundation data parameters missing"))?;
                if parameters.len() != argument_count {
                    return Err(invalid(
                        "foreign foundation refusal data application arity differs",
                    ));
                }
                if visited.insert(*id) {
                    let nominal = registry
                        .nominal(*id)
                        .ok_or_else(|| invalid("foreign foundation refusal data missing"))?;
                    charge(work, nominal.constructors.len())?;
                    for constructor in &nominal.constructors {
                        if let Some(payload) = registry
                            .constructor(*constructor)
                            .and_then(|constructor| constructor.payload.as_ref())
                        {
                            pending.push(payload);
                        }
                    }
                }
            }
            _ if argument_count != 0 => {
                return Err(invalid(
                    "foreign foundation refusal data requires a nominal application",
                ));
            }
            Type::Tuple(fields) => {
                charge(work, fields.len())?;
                pending.extend(fields.iter());
            }
            Type::Variable(id)
                if registry
                    .type_variable(*id)
                    .is_some_and(|parameter| parameter.kind == Kind::Type) => {}
            Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit => {}
            _ => return Err(invalid("foreign foundation refusal data kind differs")),
        }
    }
    Ok(())
}

fn nominal_application(id: NominalTypeId, arguments: impl IntoIterator<Item = Type>) -> Type {
    arguments
        .into_iter()
        .fold(Type::Nominal(id), |function, argument| {
            Type::Application(Box::new(function), Box::new(argument))
        })
}
fn application(ty: &Type) -> (&Type, Vec<&Type>) {
    let mut head = ty;
    let mut arguments = Vec::new();
    while let Type::Application(function, argument) = head {
        arguments.push(argument.as_ref());
        head = function;
    }
    arguments.reverse();
    (head, arguments)
}
fn at_path<'a>(mut ty: &'a Type, path: &[usize]) -> Option<&'a Type> {
    for &index in path {
        let Type::Tuple(fields) = ty else { return None };
        ty = fields.get(index)?;
    }
    Some(ty)
}
fn validate_operation(
    registry: &ResolvedRegistry,
    fact: &ForeignModuleFact,
    effect: &ResolvedEffectDeclaration,
    signature: &Type,
    metadata: &ForeignOperationDeclaration,
    work: &mut crate::types::TypeWorkBudget,
) -> Result<(), ForeignRegistrationError> {
    let Type::Function(domain, result) = signature else {
        return Err(invalid("foreign operation requires one pure arrow"));
    };
    let mut actual_state_paths = Vec::new();
    let mut domains = vec![(domain.as_ref(), Vec::<usize>::new())];
    while let Some((ty, path)) = domains.pop() {
        charge(work, path.len().saturating_add(1))?;
        let (head, _) = application(ty);
        if matches!(head,Type::Nominal(id) if fact.states.iter().any(|state|state.id==*id)) {
            actual_state_paths.push(path);
        } else if let Type::Tuple(fields) = ty {
            for (index, field) in fields.iter().enumerate() {
                let mut child = path.clone();
                child.push(index);
                domains.push((field, child));
            }
        } else {
            validate_independent_data(registry, fact, effect, ty, work)?;
        }
    }
    if actual_state_paths.len() != metadata.state_operands.len()
        || actual_state_paths
            .iter()
            .any(|path| !metadata.state_operands.contains(path))
    {
        return Err(invalid(
            "foreign domain has undeclared native state operands",
        ));
    }
    let mut seen_paths = HashSet::new();
    for path in &metadata.state_operands {
        if !seen_paths.insert(path) {
            return Err(invalid("duplicate foreign state operand"));
        }
        let state = at_path(domain, path)
            .ok_or_else(|| invalid("foreign state operand path is invalid"))?;
        let (head, arguments) = application(state);
        let Type::Nominal(id) = head else {
            return Err(invalid("foreign state operand is not a native nominal"));
        };
        let state_fact = fact
            .states
            .iter()
            .find(|state| state.id == *id)
            .ok_or_else(|| invalid("foreign state operand is not registered"))?;
        if arguments.len()!=state_fact.parameter_count || arguments.iter().any(|argument| !matches!(argument,Type::Variable(id) if effect.parameters.iter().any(|parameter|parameter.id==*id))) {return Err(invalid("foreign state operand lineage differs"));}
    }
    let domain_count = match domain.as_ref() {
        Type::Tuple(fields) => fields.len(),
        _ => 1,
    };
    let mut retained = HashSet::new();
    for &position in &metadata.retained_arguments {
        if position >= domain_count || !retained.insert(position) {
            return Err(invalid("foreign retained argument position is invalid"));
        }
    }
    match &metadata.result {
        ForeignResultRelation::Independent => {
            if metadata.state_operands.is_empty() {
                return Err(invalid("borrow operation requires registered state"));
            }
            validate_independent_data(registry, fact, effect, result, work)?;
        }
        ForeignResultRelation::Acquire {
            state,
            error,
            report,
            ..
        }
        | ForeignResultRelation::Finish {
            state,
            error,
            report,
        } => {
            let nominal = registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == *state)
                .ok_or_else(|| invalid("foreign result state missing"))?;
            let state_fact = fact
                .states
                .iter()
                .find(|state| state.id == nominal.id)
                .ok_or_else(|| invalid("foreign result state is not opaque native state"))?;
            if state_fact.parameter_count != effect.parameters.len()
                || metadata.owned_identity_position != 0
            {
                return Err(invalid("foreign owner identity or state lineage differs"));
            }
            let state_type = nominal_application(
                nominal.id,
                effect
                    .parameters
                    .iter()
                    .map(|parameter| Type::Variable(parameter.id)),
            );
            let error_id = *fact
                .data_types
                .get(error)
                .ok_or_else(|| invalid("foreign lifecycle error missing"))?;
            let report_id = *fact
                .data_types
                .get(report)
                .ok_or_else(|| invalid("foreign lifecycle report missing"))?;
            let expected =
                nominal_application(report_id, [state_type.clone(), Type::Nominal(error_id)]);
            if result.as_ref() != &expected {
                return Err(invalid(
                    "foreign lifecycle signature differs from report relation",
                ));
            }
            validate_independent_data(registry, fact, effect, &Type::Nominal(error_id), work)?;
            validate_report(registry, report_id, metadata.role)?;
            if metadata.role == ForeignOperationRole::Finish
                && (metadata.state_operands != [Vec::<usize>::new()]
                    || domain.as_ref() != &state_type)
            {
                return Err(invalid("foreign finisher does not own its exact state"));
            }
            if let ForeignResultRelation::Acquire {
                retained_parameters,
                ..
            } = &metadata.result
            {
                let mut retained = HashSet::new();
                for &position in retained_parameters {
                    if position >= effect.parameters.len()
                        || position == metadata.owned_identity_position
                        || !retained.insert(position)
                    {
                        return Err(invalid(
                            "foreign acquired state dependency position is invalid",
                        ));
                    }
                }
                // P-1 native state parameters are owner lineage coordinates.
                // Every coordinate after the owned identity remains a dependency.
                if retained.len() != effect.parameters.len().saturating_sub(1) {
                    return Err(invalid(
                        "foreign acquired state omits retained owner lineage",
                    ));
                }
            }
        }
    }
    Ok(())
}
fn validate_independent_data(
    registry: &ResolvedRegistry,
    fact: &ForeignModuleFact,
    effect: &ResolvedEffectDeclaration,
    root: &Type,
    budget: &mut crate::types::TypeWorkBudget,
) -> Result<(), ForeignRegistrationError> {
    let mut pending = vec![root];
    let mut visited = HashSet::new();
    let mut work = 0;
    while let Some(ty) = pending.pop() {
        charge(budget, 1)?;
        work += 1;
        if work > 8192 {
            return Err(invalid("foreign result relation budget exceeded"));
        }
        match ty {
            Type::Nominal(id) => {
                if fact.states.iter().any(|state| state.id == *id) {
                    return Err(invalid("independent foreign result contains native state"));
                }
                if fact.manifest.schema.foundation.is_some() {
                    charge(budget, fact.data_types.len())?;
                    if !fact.data_types.values().any(|ordinary| ordinary == id) {
                        return Err(invalid(
                            "independent foreign result contains an opaque foreign category",
                        ));
                    }
                }
                if visited.insert(*id) {
                    let nominal = registry
                        .nominal(*id)
                        .ok_or_else(|| invalid("independent foreign result is not local data"))?;
                    for id in nominal.constructors.iter() {
                        if let Some(payload) = registry
                            .constructor(*id)
                            .and_then(|constructor| constructor.payload.as_ref())
                        {
                            pending.push(payload);
                        }
                    }
                }
            }
            Type::Variable(id)
                if effect
                    .parameters
                    .iter()
                    .any(|parameter| parameter.id == *id) =>
            {
                return Err(invalid(
                    "independent foreign result contains owner identity",
                ));
            }
            Type::Application(function, argument) => {
                pending.push(function);
                pending.push(argument)
            }
            Type::Tuple(fields) => pending.extend(fields.iter()),
            Type::Bytes
            | Type::String
            | Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Variable(_) => {}
            _ => return Err(invalid("independent foreign result is not ordinary data")),
        }
    }
    Ok(())
}
fn validate_report(
    registry: &ResolvedRegistry,
    id: NominalTypeId,
    role: ForeignOperationRole,
) -> Result<(), ForeignRegistrationError> {
    let parameters = registry
        .nominal_parameters(id)
        .ok_or_else(|| invalid("lifecycle report parameters missing"))?;
    let [state, error] = parameters else {
        return Err(invalid("lifecycle report must bind state and error"));
    };
    let state = Type::Variable(state.id);
    let error = Type::Variable(error.id);
    let expected = match role {
        ForeignOperationRole::Acquire => vec![Some(state), Some(error)],
        ForeignOperationRole::Finish => vec![
            None,
            Some(error.clone()),
            Some(Type::Tuple(vec![state, error].into_boxed_slice())),
        ],
        ForeignOperationRole::Borrow => return Err(invalid("borrow has no lifecycle report")),
    };
    let nominal = registry
        .nominal(id)
        .ok_or_else(|| invalid("lifecycle report nominal missing"))?;
    if nominal.constructors.len() != expected.len() {
        return Err(invalid("lifecycle report constructor count differs"));
    }
    for (id, payload) in nominal.constructors.iter().zip(expected) {
        if registry
            .constructor(*id)
            .and_then(|constructor| constructor.payload.as_ref())
            != payload.as_ref()
        {
            return Err(invalid("lifecycle report constructor shape differs"));
        }
    }
    Ok(())
}

fn bind_state_lineage(
    signature: &Type,
    metadata: &ForeignOperationDeclaration,
    effect: &ResolvedEffectDeclaration,
) -> Vec<ForeignStateOperandFact> {
    let Type::Function(domain, _) = signature else {
        unreachable!("validated foreign pure arrow")
    };
    metadata
        .state_operands
        .iter()
        .map(|path| {
            let (head, arguments) =
                application(at_path(domain, path).expect("validated operand path"));
            let Type::Nominal(state) = head else {
                unreachable!("validated native state")
            };
            ForeignStateOperandFact {
                path: path.clone(),
                state: *state,
                lineage: arguments
                    .iter()
                    .map(|argument| {
                        effect
                            .parameters
                            .iter()
                            .position(|parameter| **argument == Type::Variable(parameter.id))
                            .expect("validated state lineage")
                    })
                    .collect(),
            }
        })
        .collect()
}
fn bind_result(
    relation: &ForeignResultRelation,
    registry: &ResolvedRegistry,
    fact: &ForeignModuleFact,
) -> ForeignResultFact {
    match relation {
        ForeignResultRelation::Independent => ForeignResultFact::Independent,
        ForeignResultRelation::Acquire {
            state,
            error,
            report,
            retained_parameters,
        } => {
            let state = registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == *state)
                .expect("validated state")
                .id;
            let report = fact.data_types[report];
            ForeignResultFact::Acquire {
                state,
                error: fact.data_types[error],
                report,
                constructors: registry
                    .nominal(report)
                    .expect("validated report")
                    .constructors
                    .to_vec(),
                retained_parameters: retained_parameters.clone(),
            }
        }
        ForeignResultRelation::Finish {
            state,
            error,
            report,
        } => {
            let state = registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == *state)
                .expect("validated state")
                .id;
            let report = fact.data_types[report];
            ForeignResultFact::Finish {
                state,
                error: fact.data_types[error],
                report,
                constructors: registry
                    .nominal(report)
                    .expect("validated report")
                    .constructors
                    .to_vec(),
            }
        }
    }
}
fn data(
    name: &str,
    parameters: &[&str],
    constructors: &[(&str, Option<&str>)],
) -> ForeignTypeDeclaration {
    ForeignTypeDeclaration {
        name: name.into(),
        parameters: parameters
            .iter()
            .map(|parameter| (*parameter).into())
            .collect(),
        category: ForeignTypeCategory::Data,
        constructors: constructors
            .iter()
            .map(|(name, payload)| ForeignConstructorDeclaration {
                name: (*name).into(),
                payload: payload.map(str::to_owned),
            })
            .collect(),
    }
}
fn state(name: &str, parameters: &[&str]) -> ForeignTypeDeclaration {
    ForeignTypeDeclaration {
        name: name.into(),
        parameters: parameters
            .iter()
            .map(|parameter| (*parameter).into())
            .collect(),
        category: ForeignTypeCategory::State,
        constructors: Vec::new(),
    }
}
fn operation(
    name: &str,
    signature: &str,
    role: ForeignOperationRole,
    state_operands: Vec<Vec<usize>>,
    result: ForeignResultRelation,
) -> ForeignOperationDeclaration {
    ForeignOperationDeclaration {
        name: name.into(),
        signature: signature.into(),
        role,
        owned_identity_position: 0,
        state_operands,
        retained_arguments: Vec::new(),
        result,
    }
}
/// Builds the registered sealed generic state-access primitive manifest.
/// # Errors
/// Returns a manifest error if its authored declaration schema is invalid.
pub fn provider_manifest(
    id: ForeignRegistrationId,
) -> Result<ForeignManifest, ForeignRegistrationError> {
    ForeignManifest::new(
        "@foreign.provider",
        id,
        ForeignManifestSchema {
            state_access: Some(ForeignStateAccessDeclaration {
                interface: "StateAccess".into(),
                method: "state_of".into(),
            }),
            ..ForeignManifestSchema::default()
        },
    )
}

#[cfg(test)]
mod storage_tests {
    use super::*;
    use crate::{
        module::ModuleId,
        source::{ByteRange, SourceFile},
        types::{reset_type_discard_observation, type_discard_visits},
    };

    #[test]
    fn final_shared_foreign_fact_disposes_recursive_metadata_iteratively() {
        const DEPTH: usize = 32_768;
        let source = SourceFile::new("foreign-storage", "()").unwrap();
        let span = source.span(ByteRange::new(0, 2).unwrap()).unwrap();
        let deep_origin = || {
            (0..DEPTH).fold(Origin::Source(span), |primary, _| Origin::Related {
                primary: Box::new(primary),
                related: Vec::new(),
            })
        };
        let signature = (0..DEPTH).fold(Type::Unit, |ty, _| {
            Type::Application(Box::new(ty), Box::new(Type::Unit))
        });
        let module = ModuleId::new(0);
        let interface = InterfaceId::new(module, 0);
        let admission = || ForeignModuleAdmission {
            module_id: module,
            registration_id: ForeignRegistrationId::new(0),
            manifest_digest: [0; 32],
            origin: deep_origin(),
        };
        // This fixture exercises storage disposal only; it is never admitted.
        let fact = Arc::new(ForeignModuleFact {
            canonical_registry: Arc::new(ResolvedRegistry::default()),
            canonical_interfaces: vec![ResolvedInterfaceDeclaration {
                id: interface,
                public: false,
                spelling: "storage".into(),
                parameters: Box::new([]).into(),
                determination: None,
                methods: Box::new([]),
                origin: deep_origin(),
                span,
            }],
            canonical_admission: admission(),
            manifest: Arc::new(sqlite_manifest(ForeignRegistrationId::new(0)).unwrap()),
            admission: admission(),
            states: vec![ForeignStateFact {
                id: NominalTypeId::new(source.id(), 0),
                parameter_count: 0,
                owned_identity_position: 0,
                origin: deep_origin(),
            }],
            data_types: BTreeMap::new(),
            constructors: BTreeMap::new(),
            effects: Vec::new(),
            operations: vec![ForeignOperationFact {
                id: OperationId::new(EffectId::new(module, 0), 0),
                role: ForeignOperationRole::Borrow,
                owned_identity_position: 0,
                state_operands: Vec::new(),
                state_lineage: Vec::new(),
                retained_arguments: Vec::new(),
                result: ForeignResultFact::Independent,
                signature,
                origin: deep_origin(),
            }],
            state_access: Some(ForeignStateAccessFact {
                interface,
                method: MethodId::new(interface, 0),
                origin: deep_origin(),
            }),
            layout: None,
            storage: None,
        });
        let retained = Arc::clone(&fact);
        let replacement_access = ForeignStateAccessFact {
            interface,
            method: MethodId::new(interface, 0),
            origin: deep_origin(),
        };
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut retained = retained;
                reset_type_discard_observation();
                drop(fact);
                assert_eq!(type_discard_visits(), 0);
                assert_eq!(Arc::strong_count(&retained), 1);
                assert_eq!(retained.operations.len(), 1);
                assert!(matches!(
                    retained.operations[0].signature,
                    Type::Application(..)
                ));
                assert_eq!(retained.states.len(), 1);
                assert!(matches!(retained.admission.origin, Origin::Related { .. }));
                Arc::get_mut(&mut retained)
                    .unwrap()
                    .set_state_access(replacement_access);
                assert_eq!(type_discard_visits(), 0);
                drop(retained);
                assert_eq!(type_discard_visits(), 2 * DEPTH + 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

pub(crate) mod source_bindings;
