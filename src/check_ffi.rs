//! Optional checks of authored foreign facts against supplied C headers.
//!
//! The catalogue contains the original passive declarations from a complete
//! checked source closure. Mappings only select checks; neither mappings nor
//! generated C are consumed by runtime preparation, images or Rust bridges.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    fs::{self, File},
    io::Read,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::Arc,
};

use serde::{Deserialize, Serialize, ser::SerializeSeq};

use crate::{
    driver::{FileFailure, RunConfiguration, compile_path_for_ffi},
    foreign::source_contract::{
        PreparedAbiResult, PreparedAddressRepresentation, PreparedForeignLibrary,
        PreparedForeignSymbol, PreparedOperandSource, PreparedRepresentation,
        PreparedScalarRepresentation, PreparedScalarValue,
    },
    module::LoadedModule,
    source::{SourceFile, Span},
    types::TypeWorkBudget,
};

const TARGET: &str = "x86_64-unknown-linux-gnu";

/// Explicit inputs for optional, compile-only header verification.
#[derive(Debug)]
pub struct CheckConfiguration {
    pub headers: Vec<PathBuf>,
    pub mapping: PathBuf,
    pub compiler: PathBuf,
    pub output: PathBuf,
    pub target: String,
}

impl CheckConfiguration {
    #[must_use]
    pub fn new(mapping: PathBuf, compiler: PathBuf, output: PathBuf) -> Self {
        Self {
            headers: Vec::new(),
            mapping,
            compiler,
            output,
            target: TARGET.into(),
        }
    }
}

/// Successful checks retain authoring text and diagnostics, never an object.
#[derive(Debug)]
pub struct CheckedHeaders {
    source: PathBuf,
    log: PathBuf,
    declarations: usize,
}

impl CheckedHeaders {
    #[must_use]
    pub fn generated_source(&self) -> &Path {
        &self.source
    }
    #[must_use]
    pub fn compiler_log(&self) -> &Path {
        &self.log
    }
    #[must_use]
    pub const fn declaration_count(&self) -> usize {
        self.declarations
    }
}

/// A causal input, source-compilation, declaration or C-tool failure.
#[derive(Debug)]
pub struct CheckFailure {
    reason: &'static str,
    detail: String,
    source: Option<Box<FileFailure>>,
    declaration: Option<(Arc<SourceFile>, Span)>,
    log: Option<PathBuf>,
}

impl CheckFailure {
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        self.reason
    }
    #[must_use]
    pub fn source_failure(&self) -> Option<&FileFailure> {
        self.source.as_deref()
    }
    #[must_use]
    pub fn declaration(&self) -> Option<(&SourceFile, Span)> {
        self.declaration
            .as_ref()
            .map(|(source, span)| (source.as_ref(), *span))
    }
    #[must_use]
    pub fn compiler_log(&self) -> Option<&Path> {
        self.log.as_deref()
    }
}

impl fmt::Display for CheckFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.detail)
    }
}
impl Error for CheckFailure {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.source.as_deref().map(|source| source as &dyn Error)
    }
}

fn failure(reason: &'static str, detail: impl Into<String>) -> CheckFailure {
    CheckFailure {
        reason,
        detail: detail.into(),
        source: None,
        declaration: None,
        log: None,
    }
}

fn resource() -> CheckFailure {
    failure(
        "check-ffi.resource",
        "header-check work or storage was refused",
    )
}

fn pay(work: &mut TypeWorkBudget, units: usize) -> Result<(), CheckFailure> {
    work.charge(units).map_err(|()| resource())
}

pub(crate) struct CheckedForeignModule {
    path: PathBuf,
    source: Arc<SourceFile>,
    libraries: Vec<Arc<PreparedForeignLibrary>>,
}

pub(crate) fn retain_module(
    catalogue: &mut Vec<CheckedForeignModule>,
    module: &LoadedModule,
    libraries: Vec<Arc<PreparedForeignLibrary>>,
    work: &mut TypeWorkBudget,
) -> Result<(), ()> {
    if libraries.is_empty() {
        return Ok(());
    }
    let bytes = module.canonical_path().as_os_str().len();
    work.charge(bytes.checked_add(2).ok_or(())?)?;
    catalogue.try_reserve_exact(1).map_err(|_| ())?;
    let mut path = PathBuf::new();
    path.try_reserve_exact(bytes).map_err(|_| ())?;
    path.push(module.canonical_path());
    catalogue.push(CheckedForeignModule {
        path,
        source: Arc::clone(module.retained_source()),
        libraries,
    });
    Ok(())
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
enum Role {
    Representation,
    Constant,
    Sentinel,
    Owner,
    Access,
    Symbol,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MappingFile {
    version: u32,
    declarations: Vec<Mapping>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Mapping {
    module: PathBuf,
    library: String,
    kind: Role,
    member: String,
    c_type: Option<String>,
    c_name: Option<String>,
    parameters: Option<Vec<String>>,
    result: Option<String>,
}

#[derive(Clone, Copy)]
struct Declaration<'a> {
    module: &'a CheckedForeignModule,
    library: &'a PreparedForeignLibrary,
    role: Role,
    index: usize,
    name: &'a str,
    span: Span,
}

impl Declaration<'_> {
    fn failure(self, reason: &'static str, detail: impl Into<String>) -> CheckFailure {
        let mut failure = failure(reason, detail);
        failure.declaration = Some((Arc::clone(&self.module.source), self.span));
        failure
    }
}

fn read_mapping(path: &Path, work: &mut TypeWorkBudget) -> Result<MappingFile, CheckFailure> {
    let file = File::open(path).map_err(|error| {
        failure(
            "check-ffi.mapping-read",
            format!("cannot read {}: {error}", path.display()),
        )
    })?;
    let bytes = usize::try_from(
        file.metadata()
            .map_err(|error| failure("check-ffi.mapping-read", error.to_string()))?
            .len(),
    )
    .map_err(|_| resource())?;
    pay(work, bytes)?;
    let mut input = Vec::new();
    input
        .try_reserve_exact(bytes.checked_add(1).ok_or_else(resource)?)
        .map_err(|_| resource())?;
    file.take(
        u64::try_from(bytes)
            .map_err(|_| resource())?
            .checked_add(1)
            .ok_or_else(resource)?,
    )
    .read_to_end(&mut input)
    .map_err(|error| failure("check-ffi.mapping-read", error.to_string()))?;
    if input.len() != bytes {
        return Err(failure(
            "check-ffi.mapping-read",
            "mapping changed while being read",
        ));
    }
    let mapping: MappingFile = serde_json::from_slice(&input)
        .map_err(|error| failure("check-ffi.mapping-format", error.to_string()))?;
    if mapping.version != 1 {
        return Err(failure(
            "check-ffi.mapping-version",
            "supported mapping version is 1",
        ));
    }
    Ok(mapping)
}

fn declarations<'a>(
    catalogue: &'a [CheckedForeignModule],
    work: &mut TypeWorkBudget,
) -> Result<Vec<Declaration<'a>>, CheckFailure> {
    let mut result = Vec::new();
    for module in catalogue {
        for library in &module.libraries {
            macro_rules! add {
                ($method:ident, $role:ident) => {
                    pay(work, library.$method().len())?;
                    result
                        .try_reserve_exact(library.$method().len())
                        .map_err(|_| resource())?;
                    for (index, member) in library.$method().iter().enumerate() {
                        result.push(Declaration {
                            module,
                            library,
                            role: Role::$role,
                            index,
                            name: member.name(),
                            span: member.origin().primary_span(),
                        });
                    }
                };
            }
            add!(representations, Representation);
            add!(constants, Constant);
            add!(sentinels, Sentinel);
            add!(owners, Owner);
            add!(accesses, Access);
            add!(symbols, Symbol);
        }
    }
    Ok(result)
}

fn identifier(text: &str) -> bool {
    let mut bytes = text.bytes();
    matches!(bytes.next(), Some(b'A'..=b'Z' | b'a'..=b'z' | b'_'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

// Header typedefs cover function pointers and complex C declarations. Mappings
// accept type words, qualifiers and pointer stars, never C expressions or code.
fn type_spelling(text: &str) -> bool {
    let mut found = false;
    for word in text.split(|character: char| character.is_ascii_whitespace() || character == '*') {
        if word.is_empty() {
            continue;
        }
        if !identifier(word) {
            return false;
        }
        found = true;
    }
    found && text.is_ascii()
}

fn validate_mapping(
    declaration: Declaration<'_>,
    mapping: &Mapping,
    work: &mut TypeWorkBudget,
) -> Result<(), CheckFailure> {
    let bad = || {
        declaration.failure(
            "check-ffi.mapping-role",
            "mapping fields disagree with the original declaration role",
        )
    };
    match declaration.role {
        Role::Representation | Role::Owner | Role::Access => {
            if mapping.c_name.is_some() || mapping.parameters.is_some() || mapping.result.is_some()
            {
                return Err(bad());
            }
            let ty = mapping.c_type.as_deref().ok_or_else(bad)?;
            pay(work, ty.len())?;
            if !type_spelling(ty) {
                return Err(declaration.failure(
                    "check-ffi.c-spelling",
                    "C types require type words/pointers or a header typedef",
                ));
            }
        }
        Role::Constant | Role::Sentinel => {
            if mapping.c_type.is_some() || mapping.parameters.is_some() || mapping.result.is_some()
            {
                return Err(bad());
            }
            let name = mapping.c_name.as_deref().ok_or_else(bad)?;
            pay(work, name.len())?;
            if !identifier(name) {
                return Err(declaration.failure(
                    "check-ffi.c-spelling",
                    "C constant/sentinel spellings must be identifiers",
                ));
            }
        }
        Role::Symbol => {
            if mapping.c_type.is_some() {
                return Err(bad());
            }
            let name = mapping.c_name.as_deref().ok_or_else(bad)?;
            let parameters = mapping.parameters.as_deref().ok_or_else(bad)?;
            let result = mapping.result.as_deref().ok_or_else(bad)?;
            let symbol = &declaration.library.symbols()[declaration.index];
            pay(
                work,
                name.len()
                    .checked_add(symbol.native_name().len())
                    .ok_or_else(resource)?,
            )?;
            if name != symbol.native_name() || !identifier(name) {
                return Err(declaration.failure(
                    "check-ffi.symbol-name",
                    "C symbol must name the original authored native symbol",
                ));
            }
            if parameters.len() != symbol.operands().len() {
                return Err(declaration.failure(
                    "check-ffi.signature",
                    "mapped parameter count disagrees with the authored ABI",
                ));
            }
            for ty in parameters
                .iter()
                .map(String::as_str)
                .chain(std::iter::once(result))
            {
                pay(work, ty.len())?;
                if !type_spelling(ty) {
                    return Err(declaration.failure(
                        "check-ffi.c-spelling",
                        "C signature types require type words/pointers or header typedefs",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn authenticate<'a>(
    catalogue: &'a [CheckedForeignModule],
    mapping: &'a MappingFile,
    base: &Path,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(Declaration<'a>, &'a Mapping)>, CheckFailure> {
    let expected = declarations(catalogue, work)?;
    if expected.is_empty() {
        return Err(failure(
            "check-ffi.empty",
            "the checked source closure contains no foreign declarations",
        ));
    }
    let mut index = BTreeMap::new();
    let mut max_key_bytes = 0;
    for (ordinal, declaration) in expected.iter().enumerate() {
        let bytes = declaration
            .module
            .path
            .as_os_str()
            .len()
            .checked_add(declaration.library.name().len())
            .and_then(|value| value.checked_add(declaration.name.len()))
            .ok_or_else(resource)?;
        max_key_bytes = max_key_bytes.max(bytes);
        pay(
            work,
            bytes
                .checked_mul(expected.len().ilog2() as usize + 1)
                .ok_or_else(resource)?,
        )?;
        if index
            .insert(
                (
                    declaration.module.path.as_path(),
                    declaration.library.name(),
                    declaration.role,
                    declaration.name,
                ),
                ordinal,
            )
            .is_some()
        {
            return Err(resource());
        }
    }
    let mut seen = BTreeSet::new();
    let mut checks = Vec::new();
    pay(work, mapping.declarations.len())?;
    checks
        .try_reserve_exact(mapping.declarations.len())
        .map_err(|_| resource())?;
    for item in &mapping.declarations {
        let bytes = item
            .module
            .as_os_str()
            .len()
            .checked_add(item.library.len())
            .and_then(|value| value.checked_add(item.member.len()))
            .ok_or_else(resource)?;
        pay(
            work,
            bytes
                .checked_add(max_key_bytes)
                .and_then(|value| value.checked_mul(expected.len().ilog2() as usize + 1))
                .ok_or_else(resource)?,
        )?;
        let path = fs::canonicalize(base.join(&item.module)).map_err(|error| {
            failure(
                "check-ffi.declaration",
                format!(
                    "cannot locate defining module {}: {error}",
                    item.module.display()
                ),
            )
        })?;
        let key = (
            path.as_path(),
            item.library.as_str(),
            item.kind,
            item.member.as_str(),
        );
        let Some(ordinal) = index.get(&key).copied() else {
            return Err(failure(
                "check-ffi.declaration",
                format!(
                    "mapping does not select an original checked declaration: {} {}.{} ({:?})",
                    path.display(),
                    item.library,
                    item.member,
                    item.kind
                ),
            ));
        };
        let declaration = expected[ordinal];
        if !seen.insert(ordinal) {
            return Err(declaration.failure(
                "check-ffi.duplicate",
                "original declaration is mapped more than once",
            ));
        }
        validate_mapping(declaration, item, work)?;
        checks.push((declaration, item));
    }
    if let Some((_, missing)) = expected
        .iter()
        .enumerate()
        .find(|(ordinal, _)| !seen.contains(ordinal))
    {
        return Err(missing.failure(
            "check-ffi.missing",
            format!(
                "original {:?} {}.{} has no C verification mapping",
                missing.role,
                missing.library.name(),
                missing.name
            ),
        ));
    }
    Ok(checks)
}

struct Emitter {
    text: String,
    work: TypeWorkBudget,
}
impl Emitter {
    fn line(&mut self, text: &str) -> Result<(), CheckFailure> {
        pay(
            &mut self.work,
            text.len().checked_add(1).ok_or_else(resource)?,
        )?;
        self.text
            .try_reserve(text.len().checked_add(1).ok_or_else(resource)?)
            .map_err(|_| resource())?;
        self.text.push_str(text);
        self.text.push('\n');
        Ok(())
    }
    fn assertion(&mut self, expression: &str, label: &str) -> Result<(), CheckFailure> {
        self.line(&format!("_Static_assert({expression}, \"{label}\");"))
    }
    fn scalar(
        &mut self,
        ty: &str,
        representation: PreparedScalarRepresentation,
        label: &str,
    ) -> Result<(), CheckFailure> {
        let (bits, signed) = match representation {
            PreparedScalarRepresentation::Signed(bits) => (bits, true),
            PreparedScalarRepresentation::Unsigned(bits) => (bits, false),
            PreparedScalarRepresentation::SizeT => (64, false),
        };
        self.assertion(
            &format!("__builtin_classify_type({ty}) == __builtin_classify_type(int)"),
            label,
        )?;
        self.assertion(&format!("sizeof({ty}) * CHAR_BIT == {bits}"), label)?;
        if representation == PreparedScalarRepresentation::SizeT {
            self.assertion(
                &format!("__builtin_types_compatible_p({ty}, size_t)"),
                label,
            )?;
        }
        self.assertion(
            &format!("((({ty})-1) < (({ty})0)) == {}", u8::from(signed)),
            label,
        )
    }
    fn representation(
        &mut self,
        ty: &str,
        representation: PreparedRepresentation,
        label: &str,
    ) -> Result<(), CheckFailure> {
        match representation {
            PreparedRepresentation::Scalar(scalar) => self.scalar(ty, scalar, label),
            PreparedRepresentation::Address(address) => {
                self.assertion(&format!("__builtin_classify_type({ty}) == __builtin_classify_type(void *) && sizeof({ty}) == 8"), label)?;
                let pointee = format!("__typeof__(*({ty})0)");
                match address {
                    PreparedAddressRepresentation::Opaque => self.assertion(&format!("__builtin_classify_type({pointee}) != __builtin_classify_type(__typeof__(ash_ffi_function_category))"), label),
                    PreparedAddressRepresentation::Bytes => self.assertion(&format!("__builtin_types_compatible_p({pointee}, void) || (__builtin_classify_type({pointee}) == __builtin_classify_type(int) && sizeof({pointee}) == 1)"), label),
                }
            }
            PreparedRepresentation::FunctionAddressSentinel => {
                self.assertion(&format!("__builtin_classify_type({ty}) == __builtin_classify_type(void *) && sizeof({ty}) == 8"), label)?;
                self.assertion(&format!("__builtin_classify_type(__typeof__(*({ty})0)) == __builtin_classify_type(__typeof__(ash_ffi_function_category))"), label)
            }
        }
    }
}

fn value_literal(value: PreparedScalarValue) -> String {
    format!(
        "{}((__int128){}ULL)",
        if value.negative { "-" } else { "" },
        value.magnitude
    )
}

fn symbol_checks(
    emitter: &mut Emitter,
    symbol: &PreparedForeignSymbol,
    mapping: &Mapping,
    label: &str,
    ordinal: usize,
) -> Result<(), CheckFailure> {
    let parameters = mapping.parameters.as_deref().ok_or_else(resource)?;
    for (position, (ty, operand)) in parameters.iter().zip(symbol.operands()).enumerate() {
        let alias = format!("ash_ffi_{ordinal}_arg_{position}");
        emitter.line(&format!("typedef {ty} {alias};"))?;
        if matches!(
            operand.source(),
            PreparedOperandSource::OwnerOutput | PreparedOperandSource::OffsetOutput
        ) {
            emitter.representation(
                &alias,
                PreparedRepresentation::Address(PreparedAddressRepresentation::Opaque),
                label,
            )?;
            emitter.representation(
                &format!("__typeof__(*({alias})0)"),
                operand.representation(),
                label,
            )?;
        } else {
            emitter.representation(&alias, operand.representation(), label)?;
        }
    }
    let result = mapping.result.as_deref().ok_or_else(resource)?;
    let result_alias = format!("ash_ffi_{ordinal}_result");
    emitter.line(&format!("typedef {result} {result_alias};"))?;
    match symbol.result() {
        PreparedAbiResult::Void => emitter.assertion(
            &format!("__builtin_types_compatible_p({result_alias}, void)"),
            label,
        )?,
        PreparedAbiResult::Scalar(representation) => {
            emitter.scalar(&result_alias, representation, label)?
        }
        PreparedAbiResult::Address(representation) => emitter.representation(
            &result_alias,
            PreparedRepresentation::Address(representation),
            label,
        )?,
    }
    let mut arguments = String::new();
    for position in 0..parameters.len() {
        if position != 0 {
            arguments.push_str(", ");
        }
        arguments.push_str(&format!("ash_ffi_{ordinal}_arg_{position}"));
    }
    if arguments.is_empty() {
        arguments.push_str("void");
    }
    emitter.line(&format!(
        "typedef {result_alias} (*ash_ffi_{ordinal}_signature)({arguments});"
    ))?;
    emitter.assertion(
        &format!(
            "__builtin_types_compatible_p(__typeof__(&{}), ash_ffi_{ordinal}_signature)",
            mapping.c_name.as_deref().ok_or_else(resource)?
        ),
        label,
    )
}

fn emit(
    checks: &[(Declaration<'_>, &Mapping)],
    work: TypeWorkBudget,
) -> Result<Emitter, CheckFailure> {
    let mut emitter = Emitter {
        text: String::new(),
        work,
    };
    emitter.line("/* Optional authoring checks. No runtime calls or object output. */")?;
    emitter.line("#include <stdint.h>\n#include <stddef.h>\n#include <limits.h>")?;
    emitter.line("#if !defined(__GNUC__) || __GNUC__ < 14 || !defined(__x86_64__) || !defined(__linux__) || !defined(__LP64__)\n#error check-ffi requires GNU C 14+ for x86_64-unknown-linux-gnu\n#endif")?;
    emitter.line("void ash_ffi_function_category(void);")?;
    emitter.assertion(
        "CHAR_BIT == 8 && sizeof(void *) == 8 && sizeof(size_t) == 8 && sizeof(long) == 8",
        "foreign target profile",
    )?;
    emitter.assertion(
        "__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__",
        "foreign target byte order",
    )?;
    for (ordinal, (declaration, mapping)) in checks.iter().enumerate() {
        let line = declaration
            .module
            .source
            .line_column(declaration.span.range().start())
            .map_err(|_| resource())?
            .line();
        // Numeric generated file coordinates carry only an ordinal. The exact
        // source path/range/role table is retained separately in the output.
        emitter.line(&format!("#line {line} \"ash-ffi-declaration-{ordinal}\""))?;
        let label = format!(
            "{}.{}, {:?}",
            declaration.library.name(),
            declaration.name,
            declaration.role
        );
        match declaration.role {
            Role::Representation | Role::Owner | Role::Access => {
                let ty = mapping.c_type.as_deref().ok_or_else(resource)?;
                let alias = format!("ash_ffi_{ordinal}_type");
                emitter.line(&format!("typedef {ty} {alias};"))?;
                let representation = match declaration.role {
                    Role::Representation => {
                        declaration.library.representations()[declaration.index].representation()
                    }
                    Role::Owner => PreparedRepresentation::Address(
                        declaration.library.owners()[declaration.index].representation(),
                    ),
                    Role::Access => {
                        PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
                    }
                    _ => return Err(resource()),
                };
                emitter.representation(&alias, representation, &label)?;
            }
            Role::Constant => {
                let name = mapping.c_name.as_deref().ok_or_else(resource)?;
                let constant = &declaration.library.constants()[declaration.index];
                emitter.assertion(&format!("__builtin_classify_type(__typeof__({name})) == __builtin_classify_type(int)"), &label)?;
                emitter.assertion(
                    &format!(
                        "((__int128)({name})) == {}",
                        value_literal(constant.value())
                    ),
                    &label,
                )?;
            }
            Role::Sentinel => {
                let name = mapping.c_name.as_deref().ok_or_else(resource)?;
                let sentinel = &declaration.library.sentinels()[declaration.index];
                let representation =
                    &declaration.library.representations()[sentinel.representation_index()];
                let (_, mapped) = checks
                    .iter()
                    .find(|(candidate, _)| {
                        std::ptr::eq(candidate.library, declaration.library)
                            && candidate.role == Role::Representation
                            && candidate.index == sentinel.representation_index()
                    })
                    .ok_or_else(resource)?;
                emitter.representation(
                    &format!("__typeof__({name})"),
                    representation.representation(),
                    &label,
                )?;
                emitter.assertion(
                    &format!(
                        "__builtin_types_compatible_p(__typeof__({name}), {})",
                        mapped.c_type.as_deref().ok_or_else(resource)?
                    ),
                    &label,
                )?;
                emitter.assertion(&format!("((uintptr_t)({name})) == UINTPTR_MAX"), &label)?;
            }
            Role::Symbol => symbol_checks(
                &mut emitter,
                &declaration.library.symbols()[declaration.index],
                mapping,
                &label,
                ordinal,
            )?,
        }
    }
    Ok(emitter)
}

struct DeclarationIndex<'a>(&'a [(Declaration<'a>, &'a Mapping)]);
impl Serialize for DeclarationIndex<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(Serialize)]
        struct Entry<'a> {
            ordinal: usize,
            module: &'a Path,
            library: &'a str,
            role: Role,
            member: &'a str,
            byte_start: u32,
            byte_end: u32,
        }
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for (ordinal, (declaration, _)) in self.0.iter().enumerate() {
            seq.serialize_element(&Entry {
                ordinal,
                module: &declaration.module.path,
                library: declaration.library.name(),
                role: declaration.role,
                member: declaration.name,
                byte_start: declaration.span.range().start(),
                byte_end: declaration.span.range().end(),
            })?;
        }
        seq.end()
    }
}

// Serialization shares the same finite authoring ledger as mapping validation
// and C emission. Refusal occurs before extending the output storage.
struct IndexWriter<'a> {
    bytes: Vec<u8>,
    work: &'a mut TypeWorkBudget,
}
impl std::io::Write for IndexWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.work
            .charge(bytes.len())
            .map_err(|()| std::io::Error::other("header-check work refused"))?;
        self.bytes
            .try_reserve(bytes.len())
            .map_err(std::io::Error::other)?;
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn mismatch_declaration(
    log: &Path,
    checks: &[(Declaration<'_>, &Mapping)],
    work: &mut TypeWorkBudget,
) -> Option<(Arc<SourceFile>, Span)> {
    let mut file = File::open(log).ok()?;
    let bytes = usize::try_from(file.metadata().ok()?.len())
        .ok()?
        .min(work.remaining());
    work.charge(bytes).ok()?;
    let mut text = Vec::new();
    text.try_reserve_exact(bytes).ok()?;
    std::io::Read::by_ref(&mut file)
        .take(u64::try_from(bytes).ok()?)
        .read_to_end(&mut text)
        .ok()?;
    let text = std::str::from_utf8(&text).ok()?;
    for line in text.lines() {
        let Some(rest) = line.strip_prefix("ash-ffi-declaration-") else {
            continue;
        };
        let (ordinal, _) = rest.split_once(':')?;
        let declaration = checks.get(ordinal.parse::<usize>().ok()?)?.0;
        return Some((Arc::clone(&declaration.module.source), declaration.span));
    }
    None
}

/// Checks the complete foreign catalogue of a valid entry and its imports.
///
/// # Errors
/// Preserves source compiler failures. Rejects incomplete/invalid mappings,
/// incompatible headers/target/compiler and work/storage/I/O refusal. This
/// compiles assertions only; it neither evaluates Ash nor links/calls native C.
pub fn check_path(
    source: RunConfiguration,
    configuration: CheckConfiguration,
) -> Result<CheckedHeaders, CheckFailure> {
    if configuration.target != TARGET {
        return Err(failure(
            "check-ffi.target",
            "only x86_64-unknown-linux-gnu is supported",
        ));
    }
    let (_program, catalogue) = compile_path_for_ffi(source).map_err(|source| CheckFailure {
        reason: "check-ffi.source",
        detail: source.to_string(),
        source: Some(Box::new(source)),
        declaration: None,
        log: None,
    })?;
    let mut work = TypeWorkBudget::default();
    let mapping = read_mapping(&configuration.mapping, &mut work)?;
    let checks = authenticate(
        &catalogue,
        &mapping,
        configuration
            .mapping
            .parent()
            .unwrap_or_else(|| Path::new(".")),
        &mut work,
    )?;
    if configuration.headers.is_empty() {
        return Err(failure(
            "check-ffi.header",
            "at least one explicit header is required",
        ));
    }
    let mut headers = Vec::new();
    pay(&mut work, configuration.headers.len())?;
    headers
        .try_reserve_exact(configuration.headers.len())
        .map_err(|_| resource())?;
    for header in &configuration.headers {
        pay(&mut work, header.as_os_str().len())?;
        let path = fs::canonicalize(header).map_err(|error| {
            failure(
                "check-ffi.header",
                format!("cannot read header {}: {error}", header.display()),
            )
        })?;
        File::open(&path).map_err(|error| failure("check-ffi.header", error.to_string()))?;
        headers.push(path);
    }
    let mut generated = emit(&checks, work)?;
    let mut index = IndexWriter {
        bytes: Vec::new(),
        work: &mut generated.work,
    };
    serde_json::to_writer_pretty(&mut index, &DeclarationIndex(&checks)).map_err(|_| resource())?;
    fs::create_dir_all(&configuration.output)
        .map_err(|error| failure("check-ffi.output", error.to_string()))?;
    let generated_path = configuration.output.join("check-ffi.c");
    let log_path = configuration.output.join("check-ffi.log");
    let index_path = configuration.output.join("check-ffi-declarations.json");
    fs::write(&generated_path, &generated.text)
        .map_err(|error| failure("check-ffi.output", error.to_string()))?;
    fs::write(index_path, &index.bytes)
        .map_err(|error| failure("check-ffi.output", error.to_string()))?;
    drop(index);
    let log =
        File::create(&log_path).map_err(|error| failure("check-ffi.output", error.to_string()))?;
    let mut command = Command::new(&configuration.compiler);
    command.args([
        "-std=gnu11",
        "-m64",
        "-fsyntax-only",
        "-fdiagnostics-color=never",
        "-Wstrict-prototypes",
        "-Werror",
    ]);
    for header in headers {
        command.arg("-include").arg(header);
    }
    let status = command
        .arg(&generated_path)
        .stdin(Stdio::null())
        .stdout(
            log.try_clone()
                .map_err(|error| failure("check-ffi.output", error.to_string()))?,
        )
        .stderr(log)
        .status()
        .map_err(|error| {
            failure(
                "check-ffi.compiler",
                format!(
                    "cannot launch {}: {error}",
                    configuration.compiler.display()
                ),
            )
        })?;
    if !status.success() {
        let mut failure = failure(
            "check-ffi.mismatch",
            format!(
                "C header checks failed; see {} and its declaration index",
                log_path.display()
            ),
        );
        failure.declaration = mismatch_declaration(&log_path, &checks, &mut generated.work);
        failure.log = Some(log_path);
        return Err(failure);
    }
    Ok(CheckedHeaders {
        source: generated_path,
        log: log_path,
        declarations: checks.len(),
    })
}
